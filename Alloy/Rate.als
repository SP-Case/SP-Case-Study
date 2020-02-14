module SPtest/BCF/Rate
open SPtest/BCF/Basic

sig Limit {
	dur: Int
}
fact {
	all l:Limit | l.dur > 0
}

sig RID {
	uid: Int,
	op: OpType,
}

sig Recent {
	time: Int,
}
fact {
	all r:Recent | r.time > 0
}

sig RDB {
	datas: set RID lone -> lone Recent
}

sig RReturn {
	id: RID,
	rec: Recent,
	rdb: RDB,
}

sig TReturn {
	status: bool,
	rr:RReturn
}

//删除公理(2)
pred refreshTime[rid:RID, t:Int, db:RDB, re:RReturn] {
	let r = rid.(db.datas) {
		re.rec.time = t
		//re.rop.time > 0		//添加的无意义公理
		re.rdb.datas = db.datas - rid->r + rid->re.rec
	}
}
run refreshTime for 4

//替换变量(3:u,t,t)
//删除公理(3)
pred checkRate[u,t:Int, rid:RID, o:OpType, l:Limit, db:RDB, re:bool] {
	rid.uid = u
	rid.op = o
	let r = rid.(db.datas) {
		//替换常量(3)
		sub[t, r.time] < l.dur => re = false
		sub[t, r.time] >= l.dur => re = true
		no r => re = true
	}
}

run checkRate for 4

pred testFunc[u,t:Int, rid:RID, l:Limit, db:RDB, re:TReturn] {
	//替换常量(1-未改变状态),替换变量(2:u-无法发现,t)
	checkRate[u,t,rid,TEST,l,db,re.status]	
	re.status = true => refreshTime[rid,t,db,re.rr]
}

run testFunc for 4

//assert
//在时间范围内访问两次，true/false
check assert1_3 {
	all u,t1,t2:Int, rid:RID, l:Limit, db1,db2:RDB, re1,re2:TReturn |	
		testFunc[u,t1,rid,l,db1,re1] && 
		testFunc[u,t2,rid,l,db2,re2] => {
			no db1.datas => re1.status = true
			no db1.datas && db2 = re1.rr.rdb && sub[t2,t1] < l.dur => re2.status = false
			no db1.datas && db2 = re1.rr.rdb && sub[t2,t1] >= l.dur => re2.status = true
		}
}for 20


