import Mathlib
import Submission.Work.SG.SGRepDefs
import Submission.Work.SG.RepCoh_ndvd_defs

namespace Work.SG

open Work.SG.RC
open scoped BigOperators

/-!
# `RepCoh_ndvd`: divisibility lifts from units to the whole span

If every `n • e_q` lies in the `ℤ`-span of a list of rows, then so does every vector `x` of
length `N` all of whose coordinates are divisible by `n` (write `x = ∑_q (x_q / n) • (n • e_q)`
and use linearity of the span).  The proof goes through the coefficient-function mirror `LinF`
of `RC.linC` (`RepCoh_ndvd_defs.lean`).
-/

/-- Interchange of the two sums defining `LinF` of a coefficient function that is itself a
combination of coefficient functions. -/
theorem LinF_sum (rows : List (List ℤ)) (N : ℕ) (k : ℕ → ℤ) (f : ℕ → ℕ → ℤ) (r : ℕ) :
    LinF rows (fun c => ∑ q ∈ Finset.range N, k q * f q c) r
      = ∑ q ∈ Finset.range N, k q * LinF rows (f q) r := by
  simp only [LinF]
  have h1 : ∀ c, (∑ q ∈ Finset.range N, k q * f q c) * (rows.getD c []).getD r 0
      = ∑ q ∈ Finset.range N, (k q * f q c) * (rows.getD c []).getD r 0 :=
    fun c => Finset.sum_mul _ _ _
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ q, k q * (∑ c ∈ Finset.range rows.length, f q c * (rows.getD c []).getD r 0)
      = ∑ c ∈ Finset.range rows.length, k q * (f q c * (rows.getD c []).getD r 0) :=
    fun q => Finset.mul_sum _ _ _
  simp only [h2]
  exact Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun c _ => by ring))

/-- The `vunit` sum collapses to the `r`-th term. -/
theorem sum_vunit (n : ℤ) (N : ℕ) (k : ℕ → ℤ) (r : ℕ) (hr : r < N) :
    (∑ q ∈ Finset.range N, k q * (vunit n N q).getD r 0) = k r * n := by
  rw [Finset.sum_eq_single r]
  · rw [vunit_getD n N r r hr, if_pos rfl]
  · intro b _ hne
    rw [vunit_getD n N b r hr, if_neg (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr hr) h

/-- Main linear-algebra ingredient: if each `n • e_q` lies in the span of `rows`, then any
vector of length `N` with all coordinates divisible by `n` lies in that span. -/
theorem span_of_dvd (rows : List (List ℤ)) (N : ℕ) (n : ℤ)
    (hnmem : ∀ q, q < N → InSpan rows N (vunit n N q)) :
    ∀ x : List ℤ, x.length = N → (∀ q, q < N → n ∣ x.getD q 0) → InSpan rows N x := by
  intro x _ hdvd
  classical
  let csl : ℕ → List ℤ := fun q => if hq : q < N then Classical.choose (hnmem q hq) else []
  have hcsl : ∀ q (hq : q < N), ∀ r < N, (vunit n N q).getD r 0 = linC rows (csl q) r := by
    intro q hq r hr
    have hspec := Classical.choose_spec (hnmem q hq)
    simp only [csl, dif_pos hq]
    exact hspec r hr
  let k : ℕ → ℤ := fun q => x.getD q 0 / n
  have hkx : ∀ q, q < N → x.getD q 0 = k q * n := by
    intro q hq
    simp only [k]
    exact (Int.ediv_mul_cancel (hdvd q hq)).symm
  let cs' : List ℤ :=
    (List.range rows.length).map (fun c => ∑ q ∈ Finset.range N, k q * (csl q).getD c 0)
  have hcs' : ∀ c < rows.length, cs'.getD c 0
      = ∑ q ∈ Finset.range N, k q * (csl q).getD c 0 := by
    intro c hc
    simp only [cs']
    exact getD_map_range hc
  refine ⟨cs', ?_⟩
  intro r hr
  rw [hkx r hr, linC_eq_LinF]
  rw [LinF_congr rows (f := fun c => cs'.getD c 0)
    (g := fun c => ∑ q ∈ Finset.range N, k q * (csl q).getD c 0)
    (fun c hc => hcs' c hc) r, LinF_sum]
  have hterm : ∀ q ∈ Finset.range N, k q * LinF rows (fun c => (csl q).getD c 0) r
      = k q * (vunit n N q).getD r 0 := by
    intro q hq
    have hq' : q < N := Finset.mem_range.mp hq
    congr 1
    rw [← linC_eq_LinF, ← hcsl q hq' r hr]
  rw [Finset.sum_congr rfl hterm, sum_vunit n N k r hr]

theorem RepCoh_ndvd (j : Fin 73)
    (hnmem : ∀ q, q < Work.SG.RC.N3 j → Work.SG.RC.InSpan (Work.SG.RC.BlR (Work.SG.RC.Cd j).Bl) (Work.SG.RC.N3 j) (Work.SG.RC.vunit ((Work.SG.RC.Ad j).n) (Work.SG.RC.N3 j) q)) :
    ∀ x : List ℤ, x.length = Work.SG.RC.N3 j →
      (∀ q, q < Work.SG.RC.N3 j → ((Work.SG.RC.Ad j).n : ℤ) ∣ x.getD q 0) →
      Work.SG.RC.InSpan (Work.SG.RC.BlR (Work.SG.RC.Cd j).Bl) (Work.SG.RC.N3 j) x :=
  span_of_dvd (Work.SG.RC.BlR (Work.SG.RC.Cd j).Bl) (Work.SG.RC.N3 j) ((Work.SG.RC.Ad j).n) hnmem

end Work.SG
