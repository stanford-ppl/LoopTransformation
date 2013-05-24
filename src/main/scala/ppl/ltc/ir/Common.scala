package ppl.ltc.ir

class IRValidationException extends Exception

trait HasReconstruct[T <: HasReconstruct[T]] {
  // reconstruct this node using its copy constructor with new inputs (super sketchy and copied)
  protected def reconstruct(data: Seq[_]): T = {
    val mcp = this.getClass.getMethods().filter(m => m.getName() == "copy")
    if(mcp.length != 1) throw new IRValidationException()
    mcp(0).invoke(this, (data map (d => d.asInstanceOf[java.lang.Object])):_*).asInstanceOf[T]    
  }
}
