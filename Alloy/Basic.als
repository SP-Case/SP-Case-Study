module SPtest/BCF/Basic

//手动定义Alloy中不存在的数据类型
enum bool {true, false}
sig string {}
sig null extends AbsData {}

sig AbsData {}

sig AbsDB {
	datas: set Int lone -> lone AbsData 
}

enum OpType { TEST, WD, RC, SE, DN }

