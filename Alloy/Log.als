module SPtest/BCF/Log
open SPtest/BCF/Basic

sig Log extends AbsData{
	uid: Int,
	op: OpType
}

sig LogDB {
	datas: set Int lone -> lone Log
}

sig LogReturn {
	id: Int,
	log: Log,
	ldb: LogDB,
}

sig ReturnWithLog {
	lre:LogReturn
}

//删除公理(2)
pred log[u:Int, o:OpType, db:LogDB, re:LogReturn] {
	re.id->re.log not in db.datas		
	re.log.uid = u	
	re.log.op = o	//替换常量(1)
	re.ldb.datas = db.datas + re.id->re.log
}

run log for 4

pred testFunc[u:Int, db: LogDB, re:LogReturn] {
	log[u,TEST,db,re]
}

check assert1_5 {
	all u1,u2:Int, db1,db2:LogDB, re1,re2:LogReturn |
		testFunc[u1,db1,re1] && testFunc[u2,db2,re2] => {
			re1.log.uid = u1
			re1.log.op = TEST
			re2.log.uid = u2
			re2.log.op = TEST
			db2 = re1.ldb => re2.ldb.datas = db1.datas + re1.id->re1.log + re2.id -> re2.log
		}
}for 20
