import Mathlib
import Submission.Work.SG.SGRepDefs

namespace Work.SG

/-! ## Small `toFun` bridges (private, to avoid clashing with sibling modules) -/

private theorem zrec_toFun_sub (u v : Data.V3) :
    (Data.V3.sub u v).toFun = u.toFun - v.toFun := by
  funext k; fin_cases k <;> rfl

private theorem zrec_toFun_add (u v : Data.V3) :
    (Data.V3.add u v).toFun = u.toFun + v.toFun := by
  funext k; fin_cases k <;> rfl

/-- The `c`-th coordinate of the flat target expression, in terms of the raw data. -/
private theorem zrec_toFun_target (A : Data.M3) (u v w : Fin 3 → ℤ) (c : Fin 3) :
    (Data.V3.sub (CZ.ofFun u) (Data.V3.add (CZ.ofFun v) (Data.M3.mulV A (CZ.ofFun w)))).toFun c
      = u c - (v c + (A.toIMat.mulVec w) c) := by
  rw [zrec_toFun_sub, zrec_toFun_add, CZ.ofFun_toFun, CZ.ofFun_toFun,
      CZ.toIMat_mulV, CZ.ofFun_toFun]
  rfl

/-- **The integer cocycle-recursion identity.** Let `τ` be an integral cocycle on the point group
`arithRep j`, whose values on the listed elements `RC.e j i` are `z i / n` (`n = (Ad j).n`).
Then for every generator `g` and every element `i`, the integer vector
`z (g·i) − (z (gen g) + gMt g · z i)` is divisible by `n` componentwise. This is the cocycle
relation `τ(AB) ≡ τ(A) + A τ(B) (mod ℤ³)` multiplied by `n`. -/
theorem RepCoh_zrec (j : Fin 73) {tau : IMat → Fin 3 → ℝ}
    (hcoc : IsIntCocycle (arithRep j) tau)
    {z : ℕ → Fin 3 → ℤ}
    (hint : ∀ i, i < Work.SG.RC.N j → ∀ c, tau (Work.SG.RC.e j i) c = (z i c : ℝ) / ((Work.SG.RC.Ad j).n : ℝ)) :
    ∀ g, g < Work.SG.RC.KK j → ∀ i, i < Work.SG.RC.N j →
      Data.V3.dvd ((Work.SG.RC.Ad j).n) (Data.V3.sub (CZ.ofFun (z (Work.SG.RC.mulg j g i)))
        (Data.V3.add (CZ.ofFun (z (Work.SG.RC.geni j g))) (Data.M3.mulV (Work.SG.RC.gMt j g) (CZ.ofFun (z i)))))
        = true := by
  intro g hg i hi
  -- indices and membership in the point group
  have hm : RC.mulg j g i < RC.N j := RC.mulg_lt j g hg i hi
  have hgi : RC.geni j g < RC.N j := RC.geni_lt j g hg
  -- the cocycle relation for `G j g` and `e j i`
  obtain ⟨nn, hnn⟩ := hcoc (RC.G j g) (RC.G_mem j g hg) (RC.e j i) (RC.e_mem j i hi)
  rw [← RC.e_mulGen j g hg i hi] at hnn
  have hGtau : tau (RC.G j g) = tau (RC.e j (RC.geni j g)) := by rw [RC.e_genIdx j g hg]
  rw [hGtau] at hnn
  rw [show RC.G j g = (RC.gMt j g).toIMat from rfl] at hnn
  -- substitute the values `z · / n` of `τ` on the enumerated elements
  have hzm : tau (RC.e j (RC.mulg j g i)) =
      fun c => (z (RC.mulg j g i) c : ℝ) / ((RC.Ad j).n : ℝ) := funext (hint _ hm)
  have hzgi : tau (RC.e j (RC.geni j g)) =
      fun c => (z (RC.geni j g) c : ℝ) / ((RC.Ad j).n : ℝ) := funext (hint _ hgi)
  have hzi : tau (RC.e j i) = fun c => (z i c : ℝ) / ((RC.Ad j).n : ℝ) := funext (hint i hi)
  rw [hzm, hzgi, hzi] at hnn
  rw [RC.dvd_iff_toFun]
  intro c
  have hn0 : ((RC.Ad j).n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (RC.N_pos j).ne'
  -- pull the denominator out of the matrix--vector product
  have hsum : (∑ k, ((RC.gMt j g).toIMat c k : ℝ) * ((z i k : ℝ) / ((RC.Ad j).n : ℝ)))
      = (∑ k, ((RC.gMt j g).toIMat c k : ℝ) * (z i k : ℝ)) / ((RC.Ad j).n : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun k _ => (mul_div_assoc _ _ _).symm)
  -- the coordinatewise real equation
  have hsc : (z (RC.mulg j g i) c : ℝ) / ((RC.Ad j).n : ℝ)
      = (z (RC.geni j g) c : ℝ) / ((RC.Ad j).n : ℝ)
        + (∑ k, ((RC.gMt j g).toIMat c k : ℝ) * ((z i k : ℝ) / ((RC.Ad j).n : ℝ)))
        + (nn c : ℝ) := by
    have hc := congrFun hnn c
    simpa [Matrix.mulVec_apply, Matrix.row_apply, dotProduct, intVec, Pi.add_apply] using hc
  -- clear the denominator
  have hmul : (z (RC.mulg j g i) c : ℝ)
      = (z (RC.geni j g) c : ℝ) + (∑ k, ((RC.gMt j g).toIMat c k : ℝ) * (z i k : ℝ))
        + ((RC.Ad j).n : ℝ) * (nn c : ℝ) := by
    rw [hsum] at hsc
    field_simp at hsc
    linarith
  -- read off divisibility
  rw [zrec_toFun_target]
  refine ⟨nn c, ?_⟩
  have hcast : ((z (RC.mulg j g i) c -
        (z (RC.geni j g) c + ((RC.gMt j g).toIMat.mulVec (z i)) c) : ℤ) : ℝ)
      = ((((RC.Ad j).n : ℤ) * nn c : ℤ) : ℝ) := by
    rw [Matrix.mulVec_apply, dotProduct]
    push_cast
    simp only [Matrix.row_apply]
    linarith [hmul]
  exact Int.cast_injective hcast

end Work.SG
