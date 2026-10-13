import Mathlib
import Submission.Work.WilE4.CAD.type_local

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical Filter
open scoped Topology

namespace Work.WilE4.CAD

open MvPolynomial Polynomial

/-! Sequential closedness of the realised-sign-vector set at a limit point `x` at which the
non-degeneracy conditions hold *pointwise* (rather than in a neighbourhood of `x`).

The proof is the same as that of `realized_of_tendsto_bdd`, but only the value of `Good` at the
limit point itself is used. -/
theorem realized_of_tendsto_bdd_good {m k : ℕ} {P : Fin k → MvPolynomial (Fin (m+1)) ℝ}
    {d : Fin k → ℕ} {x : Fin m → ℝ} (hgood : Good P d x)
    {a : ℕ → Fin m → ℝ} (ha : Filter.Tendsto a Filter.atTop (nhds x))
    {w : ℕ → ℝ} {w₀ : ℝ} (hw : Filter.Tendsto w Filter.atTop (nhds w₀))
    {v : Fin k → SignType}
    (hv : ∀ᶠ n in Filter.atTop, ∀ i, SignType.sign ((q (P i) (a n)).eval (w n)) = v i) :
    realized P x v := by
  have hxg : Good P d x := hgood
  have hlim : ∀ i, Tendsto (fun n => (q (P i) (a n)).eval (w n)) atTop
      (𝓝 ((q (P i) x).eval w₀)) := fun i =>
    ((continuous_q_eval (P i)).tendsto (x, w₀)).comp (ha.prodMk_nhds hw)
  have hsub : ∀ i, v i = 0 → (q (P i) x).eval w₀ = 0 := by
    intro i hi
    have hzero : ∀ᶠ n in atTop, (q (P i) (a n)).eval (w n) = 0 :=
      hv.mono fun n hn => sign_eq_zero_iff.mp (by rw [hn i, hi])
    have h2 : Tendsto (fun n => (q (P i) (a n)).eval (w n)) atTop (𝓝 0) :=
      Filter.Tendsto.congr' (hzero.mono fun n hn => hn.symm) tendsto_const_nhds
    exact tendsto_nhds_unique (hlim i) h2
  have hJs : ∀ i j, (q (P i) x).eval w₀ = 0 → (q (P j) x).eval w₀ = 0 → i = j := by
    intro i j hi hj
    by_contra hne
    exact isCoprime_no_common_root (hxg.2.1 i j hne)
      (Polynomial.IsRoot.def.mpr hi) (Polynomial.IsRoot.def.mpr hj)
  have hsign : ∀ i, (q (P i) x).eval w₀ ≠ 0 →
      SignType.sign ((q (P i) x).eval w₀) = v i := fun i hne =>
    sign_eq_of_tendsto (hlim i) hne (hv.mono fun n hn => hn i)
  by_cases hJZ : ∀ i, ((q (P i) x).eval w₀ = 0 ↔ v i = 0)
  · refine ⟨w₀, fun i => ?_⟩
    by_cases hi : v i = 0
    · rw [(hJZ i).mpr hi, sign_zero, hi]
    · exact hsign i (fun h => hi ((hJZ i).mp h))
  · obtain ⟨i₀, hi₀L, hi₀v⟩ : ∃ i, (q (P i) x).eval w₀ = 0 ∧ v i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hJZ fun i => ⟨hc i, hsub i⟩
    have huniqJ : ∀ i, (q (P i) x).eval w₀ = 0 → i = i₀ := fun i hi => hJs i i₀ hi hi₀L
    have hsimple : (q (P i₀) x).derivative.eval w₀ ≠ 0 :=
      isCoprime_derivative_root_ne_zero (hxg.2.2 i₀) (Polynomial.IsRoot.def.mpr hi₀L)
    have hsign_ne : ∀ i, i ≠ i₀ → SignType.sign ((q (P i) x).eval w₀) = v i :=
      fun i hi => hsign i (fun h => hi (huniqJ i h))
    obtain ⟨δ, hδ, hδ'⟩ := exists_pos_eval_ne
      (s := (Finset.univ.filter (fun i : Fin k => i ≠ i₀)).image (fun i => q (P i) x))
      (y := w₀) (by
        intro p hp
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
        exact fun h0 => (Finset.mem_filter.mp hi).2 (huniqJ i h0))
    obtain ⟨z, hzd, hzs⟩ := exists_sign_eq_of_simple_root
      (Polynomial.IsRoot.def.mpr hi₀L) hsimple (v i₀) hi₀v (ε := δ / 2) (by linarith)
    refine ⟨z, fun i => ?_⟩
    by_cases hi : i = i₀
    · subst hi; exact hzs
    · have hmem : q (P i) x ∈ (Finset.univ.filter (fun i : Fin k => i ≠ i₀)).image
          (fun i => q (P i) x) :=
        Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
      obtain ⟨hd1, hd2⟩ := abs_lt.mp hzd
      have hzIoo : z ∈ Set.Ioo (w₀ - δ) (w₀ + δ) :=
        ⟨by linarith, by linarith⟩
      have hwIoo : w₀ ∈ Set.Ioo (w₀ - δ) (w₀ + δ) :=
        ⟨by linarith, by linarith⟩
      rw [sign_eq_of_nonzero_Ioo (g := fun t => (q (P i) x).eval t)
        (Polynomial.continuous (q (P i) x))
        (fun t ht => hδ' (q (P i) x) hmem t (by
          rw [abs_lt]
          exact ⟨by linarith [ht.1], by linarith [ht.2]⟩))
        (x := z) (y := w₀) hzIoo hwIoo, hsign_ne i hi]

end Work.WilE4.CAD
