module SPtest/BCF/Stop
open SPtest/BCF/Basic

sig Status {
	admin: Int,
	value: bool
}

//添加参数uid:Int
//删除公理(2)
pred estop[s:Status, u:Int, re:Status] {
	u = s.admin => re.value = false		//替换常量(1)
	u != s.admin => re.value = s.value
}

pred testFunc[s:Status, re:bool]{
	s.value = true => re = true		//替换常量(2)
	s.value = false => re = false
}

check assert1_2 {
	all u:Int, s1,s2,sre:Status, tre:bool |
		estop[s1,u,sre] && testFunc[s2,tre] => {
			u = s1.admin && s2 = sre => tre = false
			u != s1.admin && s2 = sre && s1.value = true => tre = true
		}
}for 20
