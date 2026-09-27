import Mathlib

namespace Work.KT.Cone

/-- A product of square matrices over a product ring is the identity as soon as its two
components are: if `X.map Prod.fst * Y.map Prod.fst = 1` and
`X.map Prod.snd * Y.map Prod.snd = 1`, then `X * Y = 1`. -/
theorem mulProd_eq_one {B C : Type} [Ring B] [Ring C]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (X Y : Matrix ι ι (B × C))
    (hB : X.map (Prod.fst : B × C → B) * Y.map (Prod.fst : B × C → B) = 1)
    (hC : X.map (Prod.snd : B × C → C) * Y.map (Prod.snd : B × C → C) = 1) :
    X * Y = 1 := by
  -- matrix multiplication is componentwise: it commutes with the two projections
  have hmapB : (X * Y).map (Prod.fst : B × C → B)
      = X.map (Prod.fst : B × C → B) * Y.map (Prod.fst : B × C → B) :=
    Matrix.map_mul (f := RingHom.fst B C)
  have hmapC : (X * Y).map (Prod.snd : B × C → C)
      = X.map (Prod.snd : B × C → C) * Y.map (Prod.snd : B × C → C) :=
    Matrix.map_mul (f := RingHom.snd B C)
  have hB' : (X * Y).map (Prod.fst : B × C → B) = 1 := by rw [hmapB, hB]
  have hC' : (X * Y).map (Prod.snd : B × C → C) = 1 := by rw [hmapC, hC]
  -- and the projections of the identity matrix are the identity matrices
  have hB'' : (X * Y).map (Prod.fst : B × C → B)
      = (1 : Matrix ι ι (B × C)).map (Prod.fst : B × C → B) := by
    rw [hB', Matrix.map_one (Prod.fst : B × C → B) rfl rfl]
  have hC'' : (X * Y).map (Prod.snd : B × C → C)
      = (1 : Matrix ι ι (B × C)).map (Prod.snd : B × C → C) := by
    rw [hC', Matrix.map_one (Prod.snd : B × C → C) rfl rfl]
  -- having projected to both factors, conclude by extensionality
  ext i j
  · have := congrFun (congrFun hB'' i) j
    simpa only [Matrix.map_apply] using this
  · have := congrFun (congrFun hC'' i) j
    simpa only [Matrix.map_apply] using this

end Work.KT.Cone
