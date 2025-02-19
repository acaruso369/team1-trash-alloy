var sig File {}
var sig Trash in File {}

fact init {
  no Trash
}

pred empty {
  some Trash and       // guard
  after no Trash and   // effect on Trash
  File' = File - Trash // effect on File
}

pred delete [f : File] {
  not (f in Trash)   // guard
  Trash' = Trash + f // effect on Trash
  File' = File       // frame condition on File
}

pred restore [f : File] {
  f in Trash         // guard
  Trash' = Trash - f // effect on Trash
  File' = File       // frame condition on File
}

fact trans {
  always (empty or (some f : File | delete[f] or restore[f]))
}

pred permDelete [f: File] {
  f in Trash         // guard
  Trash' = Trash - f // effect on Trash
  File' = File - f   // effect on File
}

pred directDelete [f: File] {
  f not in Trash     // guard
  Trash' = Trash     // no change in Trash
  File' = File - f   // remove file from File
}

pred duplicateFile [f: File] {
  some f             // guard
  some f' : File' | f' not in File and File' = File + f'
  Trash' = Trash     // Frame condition for Trash
}

run example {}
