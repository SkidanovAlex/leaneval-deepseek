import Mathlib
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs

namespace Work.L2F.Props

/-- FILE `Submission/Work/L2F/Props/cmtK0_le_centralizer_of_le.lean`, in `namespace Work.L2F.Props`.
If `cmtK0 F S` is contained in the centralizer of the product `S * toGL T`, then it is contained in the centralizer (in `SL(2,F)`) of `T`.  Indeed every `x ∈ cmtK0 F S` commutes both with `S` and with `S * toGL T`, whence (cancelling `S` in `GL(2,F)`) it commutes with `toGL T`, i.e. with `T`. -/
theorem cmtK0_le_centralizer_of_le (F : Type*) [Field F]
    (S : Matrix.GeneralLinearGroup (Fin 2) F) (T : Matrix.SpecialLinearGroup (Fin 2) F)
    (h : Work.L2F.Props.cmtK0 F S ≤ Work.L2F.Props.cmtK0 F (S * Matrix.SpecialLinearGroup.toGL T)) :
    Work.L2F.Props.cmtK0 F S ≤ Subgroup.centralizer ({T} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  -- `x` commutes with `S` ...
  have hxS : Matrix.SpecialLinearGroup.toGL x * S = S * Matrix.SpecialLinearGroup.toGL x :=
    (Work.L2F.Props.mem_cmtK0_iff_comm F S x).mp hx
  -- ... and with `S * toGL T`.
  have hxST : Matrix.SpecialLinearGroup.toGL x * (S * Matrix.SpecialLinearGroup.toGL T) =
      (S * Matrix.SpecialLinearGroup.toGL T) * Matrix.SpecialLinearGroup.toGL x :=
    (Work.L2F.Props.mem_cmtK0_iff_comm F (S * Matrix.SpecialLinearGroup.toGL T) x).mp (h hx)
  -- Cancelling the common left factor `S`, `x` commutes with `toGL T`.
  have h2 : S * (Matrix.SpecialLinearGroup.toGL x * Matrix.SpecialLinearGroup.toGL T) =
      S * (Matrix.SpecialLinearGroup.toGL T * Matrix.SpecialLinearGroup.toGL x) := by
    calc S * (Matrix.SpecialLinearGroup.toGL x * Matrix.SpecialLinearGroup.toGL T)
        = (S * Matrix.SpecialLinearGroup.toGL x) * Matrix.SpecialLinearGroup.toGL T := by
          rw [mul_assoc]
      _ = (Matrix.SpecialLinearGroup.toGL x * S) * Matrix.SpecialLinearGroup.toGL T := by rw [hxS]
      _ = Matrix.SpecialLinearGroup.toGL x * (S * Matrix.SpecialLinearGroup.toGL T) := by
          rw [mul_assoc]
      _ = (S * Matrix.SpecialLinearGroup.toGL T) * Matrix.SpecialLinearGroup.toGL x := hxST
      _ = S * (Matrix.SpecialLinearGroup.toGL T * Matrix.SpecialLinearGroup.toGL x) := by
          rw [mul_assoc]
  have h1 : Matrix.SpecialLinearGroup.toGL x * Matrix.SpecialLinearGroup.toGL T =
      Matrix.SpecialLinearGroup.toGL T * Matrix.SpecialLinearGroup.toGL x := mul_left_cancel h2
  -- Injectivity of `toGL` transfers this to `SL(2,F)`.
  have h3 : Matrix.SpecialLinearGroup.toGL (x * T) = Matrix.SpecialLinearGroup.toGL (T * x) := by
    rw [map_mul, map_mul, h1]
  exact Matrix.SpecialLinearGroup.toGL_injective h3

end Work.L2F.Props
