import Mathlib

namespace Work.WilC5.CutCompAux

theorem CutComp_log_prod {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (log : F → F)
    (hlog_mul : ∀ {x y : F}, 0 < x → 0 < y → log (x * y) = log x + log y)
    {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, 0 < f i) :
    log (∏ i ∈ s, f i) = ∑ i ∈ s, log (f i) := by
  classical
  -- `log 1 = 0` follows from multiplicativity applied to `1 * 1 = 1`.
  have hlog_one : log 1 = 0 := by
    have h := hlog_mul (zero_lt_one : (0 : F) < 1) (zero_lt_one : (0 : F) < 1)
    rw [mul_one] at h
    linarith
  induction s using Finset.induction_on with
  | empty => simp [hlog_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa : 0 < f a := hf a (Finset.mem_insert_self a s)
    have hfs : 0 < ∏ i ∈ s, f i :=
      Finset.prod_pos (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [hlog_mul hfa hfs, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

end Work.WilC5.CutCompAux
