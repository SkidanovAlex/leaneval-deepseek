import Mathlib
import Submission.Work.SGsep.symChk_defs

namespace Work.SGsep

open Work.SG

/-!
# `Work.SGsep.symChk_kern`

The `KernCond` half of the `sym` certificate soundness: an integer vector `u` in the left kernel
of the stacked `(1 - A_g)` (expressed as a `List.foldl` of `Data.V3.add` over the generators)
satisfies the *functional* identity `∑_g u_g · (x - A_g x) = 0` for every real `x`.

The proof is a coordinatewise computation.  The ingredients are the small bridges between the
flat types `Data.V3` / `Data.M3` and coordinate functions `Fin 3 → ℤ` (`toFun`, `toIMat`,
`tmulV`), the identification of the foldl with a `Finset.range` sum, and the linearity of
`dotRZ` in its first argument (`symChk_defs.dotRZ_mulVec`, `symChk_defs.dotRZ_sub`).
-/

/-! ## Bridges for `Data.V3` / `Data.M3` -/

theorem kern_V3_add_toFun (a b : Work.SG.Data.V3) (k : Fin 3) :
    (Work.SG.Data.V3.add a b).toFun k = a.toFun k + b.toFun k := by
  fin_cases k <;> rfl

theorem kern_V3_sub_toFun (a b : Work.SG.Data.V3) (k : Fin 3) :
    (Work.SG.Data.V3.sub a b).toFun k = a.toFun k - b.toFun k := by
  fin_cases k <;> rfl

theorem kern_V3_zero_toFun (k : Fin 3) : (Work.SG.Data.V3.zero).toFun k = 0 := by
  fin_cases k <;> rfl

/-- `Data.M3.tmulV A v` is `Aᵀ v` in coordinates: its `k`-th coordinate is `∑ i, A i k * v i`. -/
theorem kern_tmulV_toFun (A : Work.SG.Data.M3) (v : Work.SG.Data.V3) (k : Fin 3) :
    (Work.SG.Data.M3.tmulV A v).toFun k = ∑ i, A.toIMat i k * v.toFun i := by
  fin_cases k <;> simp [Work.SG.Data.M3.tmulV, Work.SG.Data.M3.toIMat, Work.SG.Data.V3.toFun,
    Fin.sum_univ_three]

/-- A `foldl` of `Data.V3.add` over `List.range N` has `k`-th coordinate the sum of the
`k`-th coordinates of its summands. -/
theorem kern_foldl_V3add_toFun (N : ℕ) (f : ℕ → Work.SG.Data.V3) (k : Fin 3) :
    (List.foldl (fun acc g => Work.SG.Data.V3.add acc (f g)) Work.SG.Data.V3.zero
      (List.range N)).toFun k = ∑ g ∈ Finset.range N, (f g).toFun k := by
  induction N with
  | zero => simp only [List.range_zero, List.foldl_nil, Finset.sum_range_zero]; fin_cases k <;> rfl
  | succ N ih =>
    have hstep : List.foldl (fun acc g => Work.SG.Data.V3.add acc (f g)) Work.SG.Data.V3.zero
        (List.range (N + 1))
        = Work.SG.Data.V3.add
            (List.foldl (fun acc g => Work.SG.Data.V3.add acc (f g)) Work.SG.Data.V3.zero
              (List.range N)) (f N) := by
      rw [List.range_succ, List.foldl_append]; rfl
    rw [hstep, Finset.sum_range_succ, kern_V3_add_toFun, ih]

/-! ## Linearity of `dotRZ` in its first argument -/

theorem kern_dotRZ_fst_sub (u v : Fin 3 → ℤ) (x : Fin 3 → ℝ) :
    dotRZ (u - v) x = dotRZ u x - dotRZ v x := by
  simp only [dotRZ, Pi.sub_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]

theorem kern_dotRZ_sum {ι : Type*} (s : Finset ι) (w : ι → Fin 3 → ℤ) (x : Fin 3 → ℝ) :
    dotRZ (fun k => ∑ g ∈ s, w g k) x = ∑ g ∈ s, dotRZ (w g) x := by
  simp only [dotRZ, Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-! ## The summand of `KernCond` and the per-generator identity -/

/-- The `g`-th summand of the `KernCond` foldl: `u_g - A_gᵀ u_g`. -/
def kernTerm (D : Work.SG.Data.ArithData) (u : List ℤ) (g : ℕ) : Work.SG.Data.V3 :=
  Work.SG.Data.V3.sub ((Work.SG.Data.blocks u).getD g Work.SG.Data.V3.zero)
    (Work.SG.Data.M3.tmulV (D.gens.getD g Work.SG.Data.M3.one)
      ((Work.SG.Data.blocks u).getD g Work.SG.Data.V3.zero))

/-- Per-generator form of the identity: `u_g · (x - A_g x) = (u_g - A_gᵀ u_g) · x`. -/
theorem kernStep (D : Work.SG.Data.ArithData) (u : List ℤ) (g : ℕ) (x : Fin 3 → ℝ) :
    dotRZ (ublk u g) (x - (toRMat ((D.gens.getD g Work.SG.Data.M3.one).toIMat)).mulVec x)
      = dotRZ ((kernTerm D u g).toFun) x := by
  rw [dotRZ_sub, dotRZ_mulVec, ← kern_dotRZ_fst_sub]
  congr 1
  funext k
  rw [Pi.sub_apply, kernTerm, kern_V3_sub_toFun, kern_tmulV_toFun, ublk]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Kernel condition ⇒ functional identity.** If the certificate vector `u` satisfies
`∑_{g<G} (u_g - A_gᵀ u_g) = 0` for the generators `A_g = D.gens g` (the `KernCond` foldl), then
`∑_{g<G} u_g · (x - A_g x) = 0` for every real `x`.
Recipe: `Work.SG.Data.V3.toFun` is coordinatewise (`![x,y,z]`); `Work.SG.Data.V3.add` /
`Work.SG.Data.V3.sub` are coordinatewise; a foldl of `Work.SG.Data.V3.add` over `List.range G`
has `i`-th coordinate `∑_{g ∈ Finset.range G}`; `Work.SG.Data.M3.tmulV A v` is `Aᵀ v`, i.e.
`(Work.SG.Data.M3.tmulV A v).toFun k = ∑ i, A.toIMat i k * v.toFun i`; finally use
`Work.SGsep.dotRZ_mulVec`, `Work.SGsep.dotRZ_sub` and `Fin.sum_univ_three`. -/
theorem symChk_kern (D : Work.SG.Data.ArithData) (u : List ℤ) (h : Work.SGsep.KernCond D u) :
    ∀ x : Fin 3 → ℝ,
      ∑ g ∈ Finset.range D.gens.length,
        Work.SGsep.dotRZ (Work.SGsep.ublk u g)
          (x - (Work.SG.toRMat ((D.gens.getD g Work.SG.Data.M3.one).toIMat)).mulVec x) = 0 := by
  intro x
  -- The kernel condition, coordinatewise: `∑_g (u_g - A_gᵀ u_g) = 0`.
  have hker : (fun k => ∑ g ∈ Finset.range D.gens.length, (kernTerm D u g).toFun k) = 0 := by
    funext k
    have h3 : List.foldl (fun acc g => Work.SG.Data.V3.add acc (kernTerm D u g))
        Work.SG.Data.V3.zero (List.range D.gens.length) = Work.SG.Data.V3.zero := h
    rw [← kern_foldl_V3add_toFun D.gens.length (kernTerm D u) k, h3]
    exact kern_V3_zero_toFun k
  -- Reduce each summand to the kernel term, then collapse the sum with `dotRZ_sum`.
  rw [Finset.sum_congr rfl (fun g _ => kernStep D u g x)]
  rw [(kern_dotRZ_sum (Finset.range D.gens.length) (fun g => (kernTerm D u g).toFun) x).symm,
    hker]
  simp [dotRZ]

end Work.SGsep
