module SPtest/BCF/Donate
open SPtest/BCF/EventM

sig Donate extends AbsData{
	uid: Int,
	eid: Int,
	amount: Int
}
fact {
	all d:Donate | d.amount > 0
}

sig DonateDB {
	datas: set Int lone -> lone Donate
}

sig DonateReturn {
	id: Int,
	d: AbsData,
	ddb: DonateDB,
}

sig DEReturn {
	dre: DonateReturn,
	ere: EventReturn,
	ure: UserReturn
}

//替换变量(6:ui,ei,n*2)
//替换操作(1+2)
//删除公理(2)
pred donate[ui,ei,n:Int, dbd:DonateDB, dbe:EventDB, dbu:UserDB, dere:DEReturn] {
	subBalance[ui,n,dbu,dere.ure]
	dere.ure.user != null => updateEvent[ui,ei,n,dbe,dere.ere]
	dere.ere.e != null => {
		dere.dre.id->dere.dre.d not in dbd.datas	
		dere.dre.d.(Donate<:uid) = ui
		dere.dre.d.eid = ei
		dere.dre.d.amount = n
		dere.dre.ddb.datas = dbd.datas + dere.dre.id->dere.dre.d
	}
	dere.ure.user = null => {
		dere.dre.d = null
		dere.ere.e = null
		dere.ere.edb = dbe
		dere.ure.udb = dbu
	}
	dere.ere.e = null => {
		dere.dre.d = null
		dere.ere.e = null
		dere.ere.edb = dbe
		dere.ure.udb = dbu
	}
}

run donate for 4

//捐赠成功，余额不足，项目已中止
check assert1_3 {
	all ui,ei,n:Int, dbd:DonateDB, dbe:EventDB, dbu:UserDB, u:User, dere:DEReturn,
		ev1,ev2: AbsData |
		getBalance[ui,dbu,u] &&
		getEvent[ei,dbe,ev1] &&
		donate[ui,ei,n,dbd,dbe,dbu,dere] &&
		getEvent[ei,dere.ere.edb,ev2] => {
			ev1.status = true && u.balance >= n => ev2.total = add[ev1.total, n]
			ev1 != null && u.balance < n => ev2.total = ev1.total
			ev1.status = false => ev2.total = ev1.total
		}
} for 20
