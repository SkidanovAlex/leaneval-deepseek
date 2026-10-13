/-
  Work.WilE2 — area E2.  The assembly of Khovanskii's theorem for EA chains.

  This module reduces the frozen statement `E2_khovanskii` to five inputs, four of which are
  proved or in flight in this directory:

  * `hbase`   — Bézout for polynomial systems (chain length `0`), `kho_base`;
  * `hsphere` — the compactness (sphere) step, `kho_sphere`;
  * `hgood`   — the genericity bundle of the proper case, `kho_good_exists`;
  * `hproper` — the proper case of the elimination (Rolle + induction hypothesis), `kho_proper`;
  * `hsard`   — the density of regular values of a rectangular `C²` map, `regular_values_dense`.

  Only `hsard` is a genuine gap in the current development (Sard's theorem for maps
  `ℝ^{m+1} → ℝ^m`); everything else is either proved here or delegated.  Once
  `regular_values_dense` is available, the frozen theorem is obtained by replacing the explicit
  hypotheses with imports.
-/
import Mathlib
import Submission.Work.WilE2.KhoGood
import Submission.Work.WilE2.KhovB
import Submission.Work.WilE2.KhovB_le_khoPoly
import Submission.Work.WilE2.KhovB_mono

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.WilE2

open Classical
open WilkiesDesign WilkiesDesign.E WilkiesConjecture

/-- **The elimination, assembled.**  Granting the five inputs listed in the header, the number of
non-degenerate zeros of a system of `n` EA polynomials in `n` variables with a chain of `r`
functions is at most `KhovB r n D`, where `D` is the sum of the total degrees. -/
theorem kho_all_of
    (hbase : ∀ (n : ℕ) (S : ESys n 0) (F : Fin n → EPoly n 0) (T : Finset (Fin n → ℝ)),
      (∀ x ∈ T, S.Nondegen F x) → T.card ≤ KhovB 0 n (∑ i, (F i).totalDegree))
    (hsphere : ∀ (n s : ℕ) (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
      (T : Finset (Fin n → ℝ)), (∀ x ∈ T, S.Nondegen F x) →
      ∃ (S' : ESys (n + 1) (s + 1)) (F' : Fin (n + 1) → EPoly (n + 1) (s + 1))
        (T' : Finset (Fin (n + 1) → ℝ)),
        IsProperMap (liftSystem S' F') ∧ (∀ z ∈ T', S'.Nondegen F' z) ∧
          (∑ i, (F' i).totalDegree) ≤ (∑ i, (F i).totalDegree) + 2 ∧ 2 * T.card ≤ T'.card)
    (hgood : ∀ (n s : ℕ) (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
      (T : Finset (Fin n → ℝ)), (∀ x ∈ T, S.Nondegen F x) → IsProperMap (liftSystem S F) →
      ∃ y : Fin n → ℝ, KhoGood S F T y)
    (hproper : ∀ (n s : ℕ) (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
      (T : Finset (Fin n → ℝ)), IsProperMap (liftSystem S F) → (∀ x ∈ T, S.Nondegen F x) →
      (∀ (n' : ℕ) (S' : ESys n' s) (F' : Fin n' → EPoly n' s) (T' : Finset (Fin n' → ℝ)),
        (∀ x ∈ T', S'.Nondegen F' x) → T'.card ≤ KhovB s n' (∑ i, (F' i).totalDegree)) →
      (∀ y : Fin n → ℝ, KhoGood S F T y →
        T.card ≤ KhovB s (n + 1) (2 * (∑ i, (F i).totalDegree) + n + 1))) :
    ∀ (r : ℕ) (n : ℕ) (S : ESys n r) (F : Fin n → EPoly n r) (T : Finset (Fin n → ℝ)),
      (∀ x ∈ T, S.Nondegen F x) → T.card ≤ KhovB r n (∑ i, (F i).totalDegree) := by
  refine fun r => Nat.rec (motive := fun r => ∀ (n : ℕ) (S : ESys n r) (F : Fin n → EPoly n r)
      (T : Finset (Fin n → ℝ)), (∀ x ∈ T, S.Nondegen F x) →
      T.card ≤ KhovB r n (∑ i, (F i).totalDegree)) ?_ ?_ r
  · exact hbase
  · intro k ih n S F T hT
    obtain ⟨S', F', T', hproperMap, hT', hdeg, hcard⟩ := hsphere n k S F T hT
    obtain ⟨y, hy⟩ := hgood (n + 1) k S' F' T' hT' hproperMap
    have hb : T'.card ≤ KhovB k (n + 2) (2 * (∑ i, (F' i).totalDegree) + (n + 2)) :=
      hproper (n + 1) k S' F' T' hproperMap hT' ih y hy
    have hb2 : KhovB k (n + 2) (2 * (∑ i, (F' i).totalDegree) + (n + 2))
        ≤ KhovB k (n + 2) (2 * (∑ i, (F i).totalDegree) + n + 6) :=
      KhovB_mono (by omega) (le_refl _) (by omega)
    have hrw : KhovB (k + 1) n (∑ i, (F i).totalDegree)
        = KhovB k (n + 2) (2 * (∑ i, (F i).totalDegree) + n + 6) := rfl
    calc T.card ≤ T'.card := by omega
      _ ≤ KhovB k (n + 2) (2 * (∑ i, (F' i).totalDegree) + (n + 2)) := hb
      _ ≤ KhovB k (n + 2) (2 * (∑ i, (F i).totalDegree) + n + 6) := hb2
      _ = KhovB (k + 1) n (∑ i, (F i).totalDegree) := hrw.symm

/-- **`E2_khovanskii`** reduced to the five inputs.  The conclusion is the frozen statement
verbatim (`khoPoly F` is the witness polynomial). -/
theorem E2_khovanskii_of_parts
    (hbase : ∀ (n : ℕ) (S : ESys n 0) (F : Fin n → EPoly n 0) (T : Finset (Fin n → ℝ)),
      (∀ x ∈ T, S.Nondegen F x) → T.card ≤ KhovB 0 n (∑ i, (F i).totalDegree))
    (hsphere : ∀ (n s : ℕ) (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
      (T : Finset (Fin n → ℝ)), (∀ x ∈ T, S.Nondegen F x) →
      ∃ (S' : ESys (n + 1) (s + 1)) (F' : Fin (n + 1) → EPoly (n + 1) (s + 1))
        (T' : Finset (Fin (n + 1) → ℝ)),
        IsProperMap (liftSystem S' F') ∧ (∀ z ∈ T', S'.Nondegen F' z) ∧
          (∑ i, (F' i).totalDegree) ≤ (∑ i, (F i).totalDegree) + 2 ∧ 2 * T.card ≤ T'.card)
    (hgood : ∀ (n s : ℕ) (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
      (T : Finset (Fin n → ℝ)), (∀ x ∈ T, S.Nondegen F x) → IsProperMap (liftSystem S F) →
      ∃ y : Fin n → ℝ, KhoGood S F T y)
    (hproper : ∀ (n s : ℕ) (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
      (T : Finset (Fin n → ℝ)), IsProperMap (liftSystem S F) → (∀ x ∈ T, S.Nondegen F x) →
      (∀ (n' : ℕ) (S' : ESys n' s) (F' : Fin n' → EPoly n' s) (T' : Finset (Fin n' → ℝ)),
        (∀ x ∈ T', S'.Nondegen F' x) → T'.card ≤ KhovB s n' (∑ i, (F' i).totalDegree)) →
      (∀ y : Fin n → ℝ, KhoGood S F T y →
        T.card ≤ KhovB s (n + 1) (2 * (∑ i, (F i).totalDegree) + n + 1))) :
    ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (f : Fin k → EAPoly k r)
      (s : Finset (Fin k → ℝ)), k + r ≤ F →
      (∀ x ∈ s, (∀ i, eaEval c (f i) x = 0) ∧
        (Matrix.of fun i j => eaEval c (eaD c j (f i)) x).det ≠ 0) →
      s.card ≤ p.eval (∑ i, atomDeg (f i)) := by
  intro F
  refine ⟨khoPoly F, fun k r c f T hkr hT => ?_⟩
  have hnd : ∀ x ∈ T, (ESys.ofChain c).Nondegen f x :=
    fun x hx => (ESys.ofChain_nondeg c f x).mpr (hT x hx)
  have h := kho_all_of hbase hsphere hgood hproper r k (ESys.ofChain c) f T hnd
  have hsum : (∑ i, atomDeg (f i)) = (∑ i, (f i).totalDegree) + k := by
    simp only [atomDeg_eq]
    rw [Finset.sum_add_distrib]
    simp
  rw [hsum]
  exact h.trans (KhovB_le_khoPoly F r k (∑ i, (f i).totalDegree) hkr)

end Work.WilE2
