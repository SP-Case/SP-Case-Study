module SPtest/BCF/Account
open SPtest/BCF/Basic

sig User extends AbsData {
	balance: Int
}

fact {
	all u:User | u.balance >= 0
}

sig UserDB {
	datas: set Int lone -> lone User
}

sig UserReturn {
	id: Int,
	user: AbsData,
	udb: UserDB,
}

pred getBalance[uid:Int, db:UserDB, u:AbsData] {
	no uid.(db.datas) => u = null
	not no uid.(db.datas) u = uid.(db.datas)
}

run getBalance for 4

//替换变量(2:uid,n)
//删除公理(2)
pred addBalance[uid,n:Int, db:UserDB, re:UserReturn] {
	n > 0
	let u = uid.(db.datas) {
		not no u => {
			re.user.balance = add[u.balance, n]
			re.udb.datas = db.datas - uid->u + uid->re.user
		}
		no u => {
			re.user = null
			re.udb = db
		}
	}
}

run addBalance for 4

//替换变量(2:uid,n)
//删除公理(2)
pred subBalance[uid,n:Int, db:UserDB, re:UserReturn] {
	n > 0
	let u = uid.(db.datas) {
		not no u && sub[u.balance, n] >= 0 => {
			re.user.balance = sub[u.balance, n]
			//re.user.balance >= 0
			re.udb.datas = db.datas - uid->u + uid->re.user
		}
		no u => {
			re.user = null
			re.udb = db
		}
		sub[u.balance, n] < 0 => {
			re.user = null
			re.udb = db
		}
	}
}

run subBalance for 4

check assert1 {
	all uid,n:Int, u1,u2:AbsData, db:UserDB, re:UserReturn |
		getBalance[uid,db,u1] &&
		addBalance[uid,n,db,re] && 
		getBalance[uid,re.udb,u2] => {
			u1 != null => u2.balance = add[u1.balance, n]
		}
}for 20

check assert2_3 {
	all uid,n:Int, u1,u2:AbsData, db:UserDB, re:UserReturn |
		getBalance[uid,db,u1] &&
		subBalance[uid,n,db,re] && 
		getBalance[uid,re.udb,u2] => {
			u1 != null && n > u1.balance => u2.balance = u1.balance
			u1 != null && n <= u1.balance => u2.balance = sub[u1.balance, n]
		}
}for 20

check assert4_5 {
	all uid,n1,n2:Int, u:AbsData, db:UserDB, re1,re2:UserReturn |
		getBalance[uid,db,u] &&
		addBalance[uid,n1,db,re1] && 
		subBalance[uid,n2,re1.udb,re2] => {
			u != null && n1 = n2 => re2.user.balance = u.balance
			u != null && n2 > add[u.balance, n1] => re2.user = null
		}
}for 20
