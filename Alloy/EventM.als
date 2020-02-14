module SPtest/BCF/EventM
open SPtest/BCF/Account

sig Event extends AbsData{
	uid: Int,
	des: string,
	target: Int,
	total: Int,
	status: bool
}

fact {
	all e:Event {
		e.total >= 0
		e.target >= 0
	}
}

sig EventDB {
	datas: set Int lone -> lone Event
}

sig EventReturn {
	id: Int,
	e: AbsData,
	edb: EventDB
}

sig EUReturn {
	ere: EventReturn,
	ure: UserReturn
}

pred getEvent[eid:Int, db:EventDB, e:AbsData] {
	no eid.(db.datas) => e = null
	not no eid.(db.datas) => e = eid.(db.datas)
}

//替换变量(2:uid,t-因未验证而无法发现)
//删除公理(6,2:des,target未验证而无法发现)
pred createEvent[u,t:Int, s:string, db:EventDB, re:EventReturn] {
	re.id->re.e not in db.datas		
	re.e.uid = u
	re.e.des = s
	re.e.target = t
	re.e.total = 0
	//re.e.total > 0		//添加的矛盾公理
	re.e.status = true	//替换常量(1)
	re.edb.datas = db.datas + re.id->re.e
}

run createEvent for 4

//替换变量(4:u,i,i,te.target-因未验证而无法发现)
//删除公理(2)
pred stopEvent[u,i:Int, db:EventDB, re:EventReturn] {
	let ev = i.(db.datas) {
		ev.uid = u && ev.status = true => {
			re.e.uid = ev.uid
			re.e.des = ev.des
			re.e.target = ev.target
			re.e.total = ev.total
			//替换常量(1)
			re.e.status = false		
			//error:删除该公理，导致状态未改变，可重复提现
			re.edb.datas = db.datas - i->ev + i->re.e
		}
		ev.uid != u => {
			re.e = null
			re.edb = db
		}
		ev.status = false => {
			re.e = null
			re.edb = db
		}
	}
}

run stopEvent for 4

//替换变量(2:i,n)
//删除公理(3)
pred updateEvent[u,i,n:Int, db:EventDB, re:EventReturn] {
	let ev = i.(db.datas) {
		ev.status = true => {
			re.e.uid = ev.uid
			re.e.des = ev.des
			re.e.target = ev.target
			re.e.total = add[ev.total, n]
			re.e.status = true	//替换常量(1)		
			re.edb.datas = db.datas - i->ev + i->re.e
		}
		ev.status = false => {
			re.e = null
			re.edb = db
		}
	}
}

run updateEvent for 4

//替换变量(2:u,i)
//替换操作(2+1)
//删除公理(1)
pred stopAndPay[u,i:Int, edb:EventDB, dbu:UserDB, re:EUReturn] {
	stopEvent[u,i,edb,re.ere]
	//eure.ere.e != null 
	//删除if条件，出现了重复提现bug
	re.ere.e != null => addBalance[u,re.ere.e.total,dbu,re.ure]
	re.ere.e = null => re.ure.user = null
	re.ere.e = null => re.ure.udb = dbu
}

run stopAndPay for 4
		
//seq:create-stop(4:status,total,uid, stop by other user)
check assert1_4 {
	all u1,u2,t:Int, s:string, db:EventDB, ere1,ere2:EventReturn |
		createEvent[u1,t,s,db,ere1] &&
		stopEvent[u2,ere1.id,ere1.edb,ere2] => {
			u1 = u2 => ere2.e.status = false
			u1 = u2 => ere2.e.total = 0
			u1 = u2 => ere2.e.uid = u2
			u1 != u2 => ere2.e = null
		}
} for 20

//seq:create-update-get(3:status,total,uid)
check assert5_7 {
	all u1,u2,t,n:Int, s:string, db:EventDB, ere1,ere2:EventReturn, e:AbsData |
		createEvent[u1,t,s,db,ere1] &&
		updateEvent[u2,ere1.id,n,ere1.edb,ere2] &&
		getEvent[ere1.id,ere2.edb,e] => {
			e.status = true
			e.total = n
			e.uid = u1
		}
} for 20

//seq:create-update-stopandpay(4:status,userbalance,total,uid)
check assert8_11 {
	all u,t,n:Int, s:string, db:EventDB, udb:UserDB, ere1,ere2:EventReturn, re:EUReturn |
		createEvent[u,t,s,db,ere1] &&
		updateEvent[u,ere1.id,n,ere1.edb,ere2] &&
		stopAndPay[u,ere1.id,ere2.edb,udb,re] => {
			re.ere.e.status = false
			re.ure.user != null => re.ure.user.balance >= n
			re.ere.e.total = n
			re.ere.e.uid = u
		}
} for 20

//缺少assert：重复中止项目以提现
