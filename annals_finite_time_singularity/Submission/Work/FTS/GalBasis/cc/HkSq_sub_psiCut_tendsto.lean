import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.GalBasis.cc.Subcut.MajDefs
import Submission.Work.FTS.GalBasis.cc.Subcut.HkIntegrand_sub_psiCut_le_sharp
import Submission.Work.FTS.GalBasis.cut.LN_slot_tendsto
import Submission.Work.FTS.GalBasis.cc.Subcut.Upart_tendsto
import Submission.Work.FTS.GalBasis.cc.Subcut.LN_indicator_wrongWeight_le
import Submission.Work.FTS.GalBasis.cc.Subcut.HkSq_le_of_ae_dominated
import Submission.Work.FTS.GalBasis.cc.Subcut.Maj_facts_and_split

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- Route (all pieces are already proved in this directory).

Write `χ_N := fun z θ => 1 - ψ N z θ`, so `f - ψ N · f = χ_N · f`.

1. `chi_facts hs` gives `K' > 0` with `|mixed b a χ_N| ≤ K'`, `mixed b a χ_N ≠ 0 → (z,θ) ∈ U_N` for
   `U_N := {z ∉ Ioo (plo N) (phiN N)} ∪ {θ ∉ Ioo (qlo N) (qhi N)}`, and — for `i ≥ 1` —
   `mixed b i χ_N ≠ 0 → θ ∈ L_N` with `L_N` the two closed angular layers
   `Icc (tlo N) (2/(N+1)) ∪ Icc (π/2 - 2/(N+1)) (thi N)` (`CutDefs`).
2. `HkIntegrand_mul_le_slots` (the Leibniz expansion `mulSlotRHS`) followed by
   `mulSlotRHS_le_localized` gives the pointwise bound on the open quadrant
   `HkIntegrand α 4 (χ_N f) z θ ≤ 650 (K'^2+1) (1_{U_N} · HkIntegrand α 4 f + 1_{L_N}(θ) · Σ_{b<4} (D_z^b f · Wt α)²)`;
   both sides vanish at `z = 0` and at `sin(2θ) = 0`, so it holds on `Iz × Iθ`.
3. The angular strip `{θ ∉ (qlo,qhi)} ∩ Iθ = [0,qlo] ∪ [qhi,π/2]` and the `z`-strip
   `{z ∉ (plo,phiN)} ∩ Iz = [0,plo] ∪ [phiN,∞)` shrink to null sets, so their `HkIntegrand α 4 f`
   mass tends to `0` by `tendsto_HkIntegrand_indicator_theta`/`_z` (`HkMem α 4 f` gives the
   domination): this is `Subcut.Upart_tendsto`.
4. For the `L_N`-terms: each wrong-weight slot on the layer is `≤ κ N` times the corresponding pure
   `D_z`-slot (`Subcut.LN_indicator_wrongWeight_le`), which makes the majorant `Maj` bounded by
   `C (1 + κ N) HkIntegrand α 4 f` and hence (a.e.) slice- and `z`-integrable; the four layer
   integrals themselves tend to `0` by `Subcut.LN_layer_tendsto`.
5. `Subcut.HkSq_le_of_ae_dominated` transfers the a.e. pointwise bound to the iterated integral and
   `Subcut.Maj_facts_and_split` computes it, leaving
   `HkSq α 4 (χ_N f) ≤ C (∫∫ 1_{U_N} HkIntegrand α 4 f + Σ_{b<4} ∫∫ 1_{L_N} (D_z^b f · Wt α)²)`,
   whose right-hand side tends to `0` by 3 and 4.  Finally `δ ↦ ε` at the outside. -/
theorem HkSq_sub_psiCut_tendsto {α : ℝ} (hα : 0 < α) {f : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hb : Work.FTS.Nonlin.BdryTraces α 4 f) {ψ : ℕ → Work.FTS.Galerkin.Fn} {K : ℝ}
    (hs : CutSpec ψ K) :
    ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Work.Spaces.HkSq α 4 (fun z θ => f z θ - ψ N z θ * f z θ) < δ := by
  intro δ hδ
  obtain ⟨C, hCpos, hCbound⟩ :=
    Subcut.HkIntegrand_sub_psiCut_le_sharp (α := α) (f := f) hs hsm
  obtain ⟨κ0, hκ0pos, hκ0le⟩ := Subcut.LN_indicator_wrongWeight_le (α := α) (f := f) (b := 0)
  obtain ⟨κ1, hκ1pos, hκ1le⟩ := Subcut.LN_indicator_wrongWeight_le (α := α) (f := f) (b := 1)
  obtain ⟨κ2, hκ2pos, hκ2le⟩ := Subcut.LN_indicator_wrongWeight_le (α := α) (f := f) (b := 2)
  obtain ⟨κ3, hκ3pos, hκ3le⟩ := Subcut.LN_indicator_wrongWeight_le (α := α) (f := f) (b := 3)
  set κ : ℕ → ℝ := fun N => κ0 N + κ1 N + κ2 N + κ3 N with hκdef
  have hκpos : ∀ N : ℕ, 0 < κ N := by
    intro N
    rw [hκdef]
    have a := hκ0pos N; have b := hκ1pos N; have c := hκ2pos N; have d := hκ3pos N
    linarith
  have hκ : ∀ b : ℕ, b ≤ 3 → ∀ N : ℕ, 1 ≤ N → ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      (LN N).indicator (fun _ => (1 : ℝ)) θ *
          (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ κ N * (Work.Spaces.DzIter b f z θ *
            (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    intro b hb3 N hN z θ hz hθ
    have hb : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega
    rcases hb with rfl | rfl | rfl | rfl
    · exact le_trans (hκ0le N hN z θ hz hθ) (mul_le_mul_of_nonneg_right
        (by rw [hκdef]; linarith [hκ1pos N, hκ2pos N, hκ3pos N]) (sq_nonneg _))
    · exact le_trans (hκ1le N hN z θ hz hθ) (mul_le_mul_of_nonneg_right
        (by rw [hκdef]; linarith [hκ0pos N, hκ2pos N, hκ3pos N]) (sq_nonneg _))
    · exact le_trans (hκ2le N hN z θ hz hθ) (mul_le_mul_of_nonneg_right
        (by rw [hκdef]; linarith [hκ0pos N, hκ1pos N, hκ3pos N]) (sq_nonneg _))
    · exact le_trans (hκ3le N hN z θ hz hθ) (mul_le_mul_of_nonneg_right
        (by rw [hκdef]; linarith [hκ0pos N, hκ1pos N, hκ2pos N]) (sq_nonneg _))
  have hUlim := Subcut.Upart_tendsto (α := α) (f := f) hsm hmem
  -- the `L`-part limit
  have hLlim : Filter.Tendsto (fun N : ℕ => ∑ b ∈ Finset.range 4,
      ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (LN N).indicator (fun _ => (1 : ℝ)) θ *
          (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2) Filter.atTop (nhds 0) := by
    have hsum : Filter.Tendsto (fun N : ℕ =>
        (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (LN N).indicator (fun _ => (1 : ℝ)) θ *
              (Work.Spaces.DzIter 0 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (LN N).indicator (fun _ => (1 : ℝ)) θ *
              (Work.Spaces.DzIter 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (LN N).indicator (fun _ => (1 : ℝ)) θ *
              (Work.Spaces.DzIter 2 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (LN N).indicator (fun _ => (1 : ℝ)) θ *
              (Work.Spaces.DzIter 3 f z θ * Work.Spaces.Wt α z θ) ^ 2)) Filter.atTop (nhds 0) := by
      have h0 := Work.FTS.GalBasis.cut.LN_slot_tendsto (α := α) (f := f) (b := 0) hα (by norm_num) hsm hmem hb
      have h1 := Work.FTS.GalBasis.cut.LN_slot_tendsto (α := α) (f := f) (b := 1) hα (by norm_num) hsm hmem hb
      have h2 := Work.FTS.GalBasis.cut.LN_slot_tendsto (α := α) (f := f) (b := 2) hα (by norm_num) hsm hmem hb
      have h3 := Work.FTS.GalBasis.cut.LN_slot_tendsto (α := α) (f := f) (b := 3) hα (by norm_num) hsm hmem hb
      have := ((h0.add h1).add h2).add h3
      simpa using this
    refine hsum.congr' ?_
    filter_upwards with N
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  -- the pointwise comparison of the majorant with `HkIntegrand α 4 f`
  have hcap : ∀ N : ℕ, 1 ≤ N → ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      Maj α C (κ N) N f z θ ≤ C * (1 + κ N) * Work.Spaces.HkIntegrand α 4 f z θ := by
    intro N hN z θ hz hθ
    classical
    rw [Maj_apply]
    have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ := Work.Spaces.HkIntegrand_nonneg α 4 f z θ
    have hindU : (UN N).indicator (fun _ => (1 : ℝ)) (z, θ) ≤ 1 := by
      rw [Set.indicator_apply]
      split_ifs with hh <;> norm_num
    have hstep : (LN N).indicator (fun _ => (1 : ℝ)) θ *
        ∑ b ∈ Finset.range 4, (zslotW α b f z θ) ^ 2 ≤ κ N * Work.Spaces.HkIntegrand α 4 f z θ := by
      by_cases hθL : θ ∈ LN N
      · rw [Set.indicator_of_mem hθL, one_mul]
        have hb : ∑ b ∈ Finset.range 4, (zslotW α b f z θ) ^ 2 ≤
            κ N * ∑ b ∈ Finset.range 4,
              (Work.Spaces.DzIter b f z θ *
                (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun b hbm => by
            simpa only [zslotW, Set.indicator_of_mem hθL, one_mul] using
              hκ b (by have := Finset.mem_range.mp hbm; omega) N hN z θ hz hθ
        refine le_trans hb ?_
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (hκpos N))
        have hsum4 : ∑ b ∈ Finset.range 4,
              (Work.Spaces.DzIter b f z θ *
                (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
          rw [Work.Spaces.HkIntegrand]
          exact le_trans
            (Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_subset_range.mpr (by norm_num)) (fun b _ _ => sq_nonneg _))
            (le_add_of_nonneg_right (Work.Spaces.hkMixedSum_nonneg α 4 f z θ))
        exact hsum4
      · rw [Set.indicator_of_notMem hθL, zero_mul]
        exact mul_nonneg (le_of_lt (hκpos N)) hHnn
    have hsummed : (UN N).indicator (fun _ => (1 : ℝ)) (z, θ) * Work.Spaces.HkIntegrand α 4 f z θ
        + (LN N).indicator (fun _ => (1 : ℝ)) θ * ∑ b ∈ Finset.range 4, (zslotW α b f z θ) ^ 2
        ≤ (1 + κ N) * Work.Spaces.HkIntegrand α 4 f z θ := by
      have h1 : (UN N).indicator (fun _ => (1 : ℝ)) (z, θ) * Work.Spaces.HkIntegrand α 4 f z θ
          ≤ 1 * Work.Spaces.HkIntegrand α 4 f z θ :=
        mul_le_mul_of_nonneg_right hindU hHnn
      rw [one_mul] at h1
      have h3 : (1 + κ N) * Work.Spaces.HkIntegrand α 4 f z θ
          = Work.Spaces.HkIntegrand α 4 f z θ + κ N * Work.Spaces.HkIntegrand α 4 f z θ := by
        ring
      rw [h3]
      exact add_le_add h1 hstep
    refine le_trans (mul_le_mul_of_nonneg_left hsummed hCpos.le) (le_of_eq ?_)
    ring
  -- the key bound, for `N ≥ 1`
  have hkey : ∀ N : ℕ, 1 ≤ N → Work.Spaces.HkSq α 4 (fun z θ => f z θ - ψ N z θ * f z θ) ≤
      C * ((∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 4 f z θ *
                (UN N).indicator (fun _ => (1 : ℝ)) (z, θ))
          + ∑ b ∈ Finset.range 4, ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              (LN N).indicator (fun _ => (1 : ℝ)) θ *
                (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    intro N hN
    set μz : Measure ℝ := volume.restrict Work.Spaces.Iz with hμz
    set μθ : Measure ℝ := volume.restrict Work.Spaces.Iθ with hμθ
    obtain ⟨hmeas, hslice, hint, hsplit⟩ :=
      Subcut.Maj_facts_and_split hsm hmem N hN hCpos (hcap N hN)
    -- the a.e. pointwise bound of the integrand by the majorant
    have hae : ∀ᵐ p ∂(μz.prod μθ),
        Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ - ψ N z θ * f z θ) p.1 p.2
          ≤ Maj α C (κ N) N f p.1 p.2 := by
      rw [MeasureTheory.ae_iff]
      have hsub : {a : ℝ × ℝ | ¬(Work.Spaces.HkIntegrand α 4
            (fun z θ => f z θ - ψ N z θ * f z θ) a.1 a.2 ≤ Maj α C (κ N) N f a.1 a.2)}
          ⊆ {p : ℝ × ℝ | p.1 ≤ 0 ∨ p.2 ≤ 0 ∨ p.2 ≥ Real.pi / 2} := by
        intro p hp
        by_contra hcon
        simp only [Set.mem_setOf_eq, not_le, not_or] at hp hcon
        exact absurd (hCbound N p.1 p.2 hcon.1 hcon.2.1 hcon.2.2) (not_le.mpr hp)
      refine measure_mono_null hsub ?_
      have hnull1 : (μz.prod μθ) {p : ℝ × ℝ | p.1 ≤ 0} = 0 := by
        rw [show {p : ℝ × ℝ | p.1 ≤ 0} = {z : ℝ | z ≤ 0} ×ˢ Set.univ from by ext p; simp,
          MeasureTheory.Measure.prod_prod (s := {z : ℝ | z ≤ 0}) (t := Set.univ), hμz, hμθ]
        have hz0 : volume ({z : ℝ | z ≤ 0} ∩ Work.Spaces.Iz) = 0 := by
          rw [show ({z : ℝ | z ≤ 0} ∩ Work.Spaces.Iz) = ({0} : Set ℝ) from by
            ext z
            simp only [Work.Spaces.Iz, Set.mem_inter_iff, Set.mem_Ici, Set.mem_setOf_eq,
              Set.mem_singleton_iff]
            constructor
            · rintro ⟨h1, h2⟩; linarith
            · intro h; subst h; exact ⟨le_refl 0, le_refl 0⟩]
          simp
        rw [MeasureTheory.Measure.restrict_apply (μ := volume) (s := Work.Spaces.Iz)
          (t := {z : ℝ | z ≤ 0}) measurableSet_Iic, hz0, zero_mul]
      have hnull2 : (μz.prod μθ)
          ({p : ℝ × ℝ | p.2 ≤ 0} ∪ {p : ℝ × ℝ | p.2 ≥ Real.pi / 2}) = 0 := by
        have hsub2 : ({p : ℝ × ℝ | p.2 ≤ 0} ∪ {p : ℝ × ℝ | p.2 ≥ Real.pi / 2})
            ⊆ Set.univ ×ˢ (Set.Iic 0 ∪ Set.Ici (Real.pi / 2)) := by
          rintro p (hp | hp)
          · exact ⟨trivial, Or.inl (by simpa using hp)⟩
          · exact ⟨trivial, Or.inr (by simpa using hp)⟩
        refine measure_mono_null hsub2 ?_
        rw [MeasureTheory.Measure.prod_prod (s := Set.univ)
            (t := (Set.Iic 0 ∪ Set.Ici (Real.pi / 2))), hμz, hμθ]
        have hθ0 : volume ((Set.Iic 0 ∪ Set.Ici (Real.pi / 2)) ∩ Work.Spaces.Iθ) = 0 := by
          have hsub : ((Set.Iic 0 ∪ Set.Ici (Real.pi / 2)) ∩ Work.Spaces.Iθ)
              ⊆ ({0, Real.pi / 2} : Set ℝ) := by
            rintro x ⟨h | h, h1, h2⟩
            · exact Or.inl (le_antisymm h (by linarith [Real.pi_pos]))
            · exact Or.inr (le_antisymm h2 h)
          refine measure_mono_null hsub ?_
          simpa only [Set.singleton_union] using
            (measure_union_null (by simp : volume ({0} : Set ℝ) = 0)
              (by simp : volume ({Real.pi / 2} : Set ℝ) = 0))
        rw [MeasureTheory.Measure.restrict_apply (μ := volume) (s := Work.Spaces.Iθ)
          (t := (Set.Iic 0 ∪ Set.Ici (Real.pi / 2)))
          (MeasurableSet.union measurableSet_Iic measurableSet_Ici), hθ0, mul_zero]
      have hunion : ({p : ℝ × ℝ | p.2 ≤ 0 ∨ p.2 ≥ Real.pi / 2})
          = {p : ℝ × ℝ | p.2 ≤ 0} ∪ {p : ℝ × ℝ | p.2 ≥ Real.pi / 2} := rfl
      rw [show {p : ℝ × ℝ | p.1 ≤ 0 ∨ p.2 ≤ 0 ∨ p.2 ≥ Real.pi / 2}
          = {p : ℝ × ℝ | p.1 ≤ 0} ∪ {p : ℝ × ℝ | p.2 ≤ 0 ∨ p.2 ≥ Real.pi / 2} from rfl]
      exact measure_union_null hnull1 (by rw [hunion]; exact hnull2)
    have hψnn : ∀ z θ : ℝ, 0 ≤ Maj α C (κ N) N f z θ := by
      intro z θ
      rw [Maj_apply]
      exact mul_nonneg hCpos.le (add_nonneg
        (mul_nonneg (Set.indicator_nonneg (fun _ _ => by norm_num) _)
          (Work.Spaces.HkIntegrand_nonneg α 4 f z θ))
        (mul_nonneg (Set.indicator_nonneg (fun _ _ => by norm_num) _)
          (Finset.sum_nonneg fun b _ => sq_nonneg _)))
    have hgnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4
        (fun z θ => f z θ - ψ N z θ * f z θ) z θ :=
      fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ
    have hJ := Subcut.HkSq_le_of_ae_dominated hgnn hψnn hmeas hae hslice hint
    exact le_trans hJ hsplit
  -- the limit of the right-hand side
  have hlim : Filter.Tendsto (fun N : ℕ => C * ((∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 f z θ *
          (UN N).indicator (fun _ => (1 : ℝ)) (z, θ))
      + ∑ b ∈ Finset.range 4, ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (LN N).indicator (fun _ => (1 : ℝ)) θ *
            (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2)) Filter.atTop (nhds 0) := by
    have h := (hUlim.add hLlim).const_mul C
    simpa [mul_add] using h
  have hev : ∀ᶠ N : ℕ in Filter.atTop, C * ((∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 f z θ *
          (UN N).indicator (fun _ => (1 : ℝ)) (z, θ))
      + ∑ b ∈ Finset.range 4, ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (LN N).indicator (fun _ => (1 : ℝ)) θ *
            (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2) < δ :=
    hlim.eventually (isOpen_Iio.mem_nhds hδ)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  exact ⟨max N₀ 1, fun N hN =>
    lt_of_le_of_lt (hkey N (le_trans (le_max_right _ _) hN))
      (hN₀ N (le_trans (le_max_left _ _) hN))⟩

end Work.FTS.GalBasis.cc
