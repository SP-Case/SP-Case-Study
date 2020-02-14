module SPtest/BCF/AccountM

open SPtest/BCF/Account
open SPtest/BCF/Rate

sig WDReturn {
	status:bool,
	ure: UserReturn,
	rre: RReturn
}

//替换变量(5)
//替换操作(1)
//删除公理(3)
//删除if(2)
pred withdraw[u,t,n:Int, rid:RID, l:Limit, dbr:RDB, dbu:UserDB, re:WDReturn] {
	checkRate[u,t,rid,WD,l,dbr,re.status]
	re.status = true => {
		refreshTime[rid,t,dbr,re.rre]
		subBalance[u,n,dbu,re.ure]
	}
	re.status = false =>  {
		re.ure.user = null
		re.ure.udb = dbu
		re.rre.rdb = dbr
	}
}
run withdraw for 4

//assert(mono)
check withdraw1_3 {
	all u,t,n:Int, rid:RID, l:Limit, dbr:RDB, dbu:UserDB, re:WDReturn |
		withdraw[u,t,n,rid,l,dbr,dbu,re] => {
			let ou = u.(dbu.datas) {
				re.status = true => re.rre.rec.time = t
				re.status = true && ou.balance >= n => re.ure.user.balance = sub[ou.balance, n]
				re.status = true && ou.balance < n => re.ure.user = null
			}
		}
}for 20

//assert(seq)
check assert1_8 {
	all u,t1,t2,n:Int, rid:RID, l:Limit, dbr:RDB, dbu:UserDB, u1,u2:User, re1,re2:WDReturn |
		getBalance[u,dbu,u1] &&
		withdraw[u,t1,n,rid,l,dbr,dbu,re1] &&
		getBalance[u,re1.ure.udb,u2] &&
		withdraw[u,t2,n,rid,l,re1.rre.rdb,re1.ure.udb,re2] => {
			no dbr.datas => re1.status = true
			no dbr.datas && sub[t2,t1] < l.dur => re2.status = false
			no dbr.datas && sub[t2,t1] < l.dur => re2.ure.user = null
			no dbr.datas && sub[t2,t1] >= l.dur => re2.status = true
			re1.status = true && u1.balance >= n => u2.balance = sub[u1.balance, n]
			u1.balance < n => u2.balance = u1.balance
			re1.status = true && re2.status = true && u1.balance >= add[n,n] => re2.ure.user.balance = sub[u2.balance, n]
			re1.status = true && u1.balance < add[n,n] => re2.ure.user = null
	}
}for 20

		
