import Mathlib
import Submission.Work.Diff.EXT.jets_bounded_of_pde
import Submission.Work.Diff.EXT.AuxL.norm_iteratedFDeriv_prod_le
import Submission.Work.Diff.EXT.AuxL.norm_fderiv_leftEndpoint_le
import Submission.Work.Diff.EXT.AuxL.norm_iteratedFDeriv_le_mixed_timeDeriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT
namespace Jets2
open Work.Diff.EXT.JetsCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem norm_iteratedFDeriv_cJet1_le {h : E → MatE (E := E)} {y : E} {a : ℕ} {M : ℝ}
    (hM : 0 ≤ M) (hsm : ContDiffAt ℝ (⊤ : ℕ∞) h y)
    (hbd : ∀ b ≤ a + 2, ‖iteratedFDeriv ℝ b h y‖ ≤ M) :
    ‖iteratedFDeriv ℝ a (cJet1 h) y‖ ≤ max 1 ((kE E) ^ 2 * M) := by
  have hM1 : 0 ≤ max 1 ((kE E) ^ 2 * M) := le_trans zero_le_one (le_max_left _ _)
  have hBM : M ≤ max 1 ((kE E) ^ 2 * M) := by
    refine le_trans ?_ (le_max_right _ _)
    have h1 : (1 : ℝ) ≤ (kE E) ^ 2 := one_le_kE_sq (E := E)
    simpa using mul_le_mul_of_nonneg_right h1 hM
  have h0 : ‖iteratedFDeriv ℝ a h y‖ ≤ max 1 ((kE E) ^ 2 * M) :=
    le_trans (hbd a (by omega)) hBM
  have hd1 : ∀ k, ‖iteratedFDeriv ℝ a (dPart1 h k) y‖ ≤ max 1 ((kE E) ^ 2 * M) := by
    intro k
    have hfd : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E => fderiv ℝ h y) y :=
      hsm.fderiv_right (hmn := by simp)
    have h1 := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fun y : E => fderiv ℝ h y)
      (c := Module.finBasis ℝ E k) (x := y) (n := a) hfd
      (WithTop.coe_le_coe.mpr (le_top : ((a : ℕ) : ℕ∞) ≤ ⊤))
    simp only [norm_iteratedFDeriv_fderiv] at h1
    have h1' : ‖iteratedFDeriv ℝ a (dPart1 h k) y‖ ≤
        ‖Module.finBasis ℝ E k‖ * ‖iteratedFDeriv ℝ (a + 1) h y‖ := h1
    have h2 : ‖Module.finBasis ℝ E k‖ * ‖iteratedFDeriv ℝ (a + 1) h y‖ ≤ kE E * M :=
      mul_le_mul (norm_basis_le_kE k) (hbd (a + 1) (by omega)) (norm_nonneg _)
        (le_trans zero_le_one (one_le_kE (E := E)))
    have h3 : kE E * M ≤ max 1 ((kE E) ^ 2 * M) := by
      refine le_trans ?_ (le_max_right _ _)
      have h1 : (1 : ℝ) ≤ (kE E) ^ 2 := one_le_kE_sq (E := E)
      calc kE E * M ≤ (kE E) ^ 2 * M := mul_le_mul_of_nonneg_right
            (by nlinarith [one_le_kE (E := E)]) hM
        _ = (kE E) ^ 2 * M := rfl
    linarith [h1', h3]
  have hd2 : ∀ k l, ‖iteratedFDeriv ℝ a (dPart2 h k l) y‖ ≤ max 1 ((kE E) ^ 2 * M) := by
    intro k l
    have hfd2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E => fderiv ℝ (dPart1 h l) y) y :=
      (contDiffAt_dPart1 hsm l).fderiv_right (hmn := by simp)
    have h1 := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ)
      (f := fun y : E => fderiv ℝ (dPart1 h l) y) (c := Module.finBasis ℝ E k) (x := y) (n := a) hfd2
      (WithTop.coe_le_coe.mpr (le_top : ((a : ℕ) : ℕ∞) ≤ ⊤))
    simp only [norm_iteratedFDeriv_fderiv] at h1
    have h1' : ‖iteratedFDeriv ℝ a (dPart2 h k l) y‖ ≤
        ‖Module.finBasis ℝ E k‖ * ‖iteratedFDeriv ℝ (a + 1) (dPart1 h l) y‖ := h1
    have hfd1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E => fderiv ℝ h y) y :=
      hsm.fderiv_right (hmn := by simp)
    have h2 := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fun y : E => fderiv ℝ h y)
      (c := Module.finBasis ℝ E l) (x := y) (n := a + 1) hfd1
      (WithTop.coe_le_coe.mpr (le_top : ((a + 1 : ℕ) : ℕ∞) ≤ ⊤))
    simp only [norm_iteratedFDeriv_fderiv] at h2
    have h2' : ‖iteratedFDeriv ℝ (a + 1) (dPart1 h l) y‖ ≤
        ‖Module.finBasis ℝ E l‖ * ‖iteratedFDeriv ℝ (a + 2) h y‖ := h2
    have h3 : ‖Module.finBasis ℝ E k‖ * (‖Module.finBasis ℝ E l‖ *
        ‖iteratedFDeriv ℝ (a + 2) h y‖) ≤ max 1 ((kE E) ^ 2 * M) := by
      have h5 : ‖iteratedFDeriv ℝ (a + 2) h y‖ ≤ M := hbd (a + 2) (by omega)
      have h8 : ‖Module.finBasis ℝ E l‖ * ‖iteratedFDeriv ℝ (a + 2) h y‖ ≤ kE E * M :=
        mul_le_mul (norm_basis_le_kE l) h5 (norm_nonneg _)
          (le_trans zero_le_one (one_le_kE (E := E)))
      have h9 : ‖Module.finBasis ℝ E k‖ * (‖Module.finBasis ℝ E l‖ *
          ‖iteratedFDeriv ℝ (a + 2) h y‖) ≤ kE E * (kE E * M) :=
        mul_le_mul (norm_basis_le_kE k) h8 (by positivity)
          (le_trans zero_le_one (one_le_kE (E := E)))
      refine le_trans h9 ?_
      rw [show kE E * (kE E * M) = (kE E) ^ 2 * M by ring]
      exact le_max_right _ _
    have h10 : ‖Module.finBasis ℝ E k‖ * ‖iteratedFDeriv ℝ (a + 1) (dPart1 h l) y‖
        ≤ ‖Module.finBasis ℝ E k‖ * (‖Module.finBasis ℝ E l‖ *
          ‖iteratedFDeriv ℝ (a + 2) h y‖) :=
      mul_le_mul_of_nonneg_left h2' (norm_nonneg _)
    exact le_trans (le_trans h1' h10) h3
  have hT1 : ‖iteratedFDeriv ℝ a (fun y : E => fun k => dPart1 h k y) y‖
      ≤ max 1 ((kE E) ^ 2 * M) := by
    simpa only [max_eq_left hM1] using
      JetsAux.norm_iteratedFDeriv_pi_le (fun k => dPart1 h k) y a
        (fun k => contDiffAt_dPart1 hsm k) hd1
  have hT2 : ‖iteratedFDeriv ℝ a (fun y : E => fun k l => dPart2 h k l y) y‖
      ≤ max 1 ((kE E) ^ 2 * M) := by
    have hinner : ∀ k : Fin (Module.finrank ℝ E),
        ‖iteratedFDeriv ℝ a (fun y : E => fun l => dPart2 h k l y) y‖
          ≤ max 1 ((kE E) ^ 2 * M) := by
      intro k
      simpa only [max_eq_left hM1] using
        JetsAux.norm_iteratedFDeriv_pi_le (fun l => dPart2 h k l) y a
          (fun l => contDiffAt_dPart2 hsm k l) (fun l => hd2 k l)
    simpa only [max_eq_left hM1] using
      JetsAux.norm_iteratedFDeriv_pi_le (fun (k : Fin (Module.finrank ℝ E)) =>
        fun y : E => fun l => dPart2 h k l y) y a
        (fun k => contDiffAt_pi' (fun l => contDiffAt_dPart2 hsm k l)) hinner
  rw [cJet1_eq]
  have hpair : ‖iteratedFDeriv ℝ a (fun y : E =>
      ((fun k => dPart1 h k y), (fun k l => dPart2 h k l y))) y‖
      ≤ max 1 ((kE E) ^ 2 * M) := by
    simpa only [max_eq_left hM1] using
      AuxL.norm_iteratedFDeriv_prod_le (C := max 1 ((kE E) ^ 2 * M))
        (fun y : E => fun k => dPart1 h k y)
        (fun y : E => fun k l => dPart2 h k l y) y a
        (contDiffAt_pi' (fun k => contDiffAt_dPart1 hsm k))
        (contDiffAt_pi' (fun k => contDiffAt_pi' (fun l => contDiffAt_dPart2 hsm k l)))
        hT1 hT2
  have hwhole : ‖iteratedFDeriv ℝ a (fun y : E => (h y,
      ((fun k => dPart1 h k y), (fun k l => dPart2 h k l y)))) y‖
      ≤ max 1 ((kE E) ^ 2 * M) := by
    simpa only [max_eq_left hM1] using
      AuxL.norm_iteratedFDeriv_prod_le (C := max 1 ((kE E) ^ 2 * M)) h
        (fun y : E => ((fun k => dPart1 h k y), (fun k l => dPart2 h k l y))) y a hsm
        (ContDiffAt.prodMk (contDiffAt_pi' (fun k => contDiffAt_dPart1 hsm k))
          (contDiffAt_pi' (fun k => contDiffAt_pi' (fun l => contDiffAt_dPart2 hsm k l))))
        h0 hpair
  exact hwhole

/-- **Uniform bound on the jets of a smooth function along a bounded set.** -/

theorem jets_inv {σ T : ℝ} (hσT : σ < T) {U : Set E} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {u : ℝ × E → MatE (E := E)}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (Set.Ico σ T ×ˢ U))
    (hspat : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ U,
        ‖iteratedFDeriv ℝ k (fun y' : E => u (t, y')) y‖ ≤ C)
    {Φ : E × JetC (E := E) → MatE (E := E)} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hpde : ∀ p ∈ (Set.Ico σ T) ×ˢ U, deriv (fun s : ℝ => u (s, p.2)) p.1 =
        Φ (p.2, sJetData u p)) :
    ∀ j N : ℕ, ∃ M : ℝ, JetsInv σ T U u j N M := by
  have hSopen : IsOpen ((Set.Ioo σ T : Set ℝ) ×ˢ U) := isOpen_Ioo.prod hU
  have hsub : ((Set.Ioo σ T : Set ℝ) ×ˢ U) ⊆ ((Set.Ico σ T : Set ℝ) ×ˢ U) :=
    Set.prod_mono Set.Ioo_subset_Ico_self (subset_refl U)
  have huS : ContDiffOn ℝ (⊤ : ℕ∞) u ((Set.Ioo σ T : Set ℝ) ×ˢ U) := hu.mono hsub
  have hpdeS : ∀ p ∈ (Set.Ioo σ T : Set ℝ) ×ˢ U,
      deriv (fun s : ℝ => u (s, p.2)) p.1 = Φ (p.2, cJet u p) := fun p hp => hpde p (hsub hp)
  have hAseq : ∀ k : ℕ, ∀ p ∈ (Set.Ioo σ T : Set ℝ) ×ˢ U,
      Dfun u (k + 1) p = Aseq Φ u k p := by
    intro k
    induction k with
    | zero =>
      intro p hp
      have h1 : Dfun u 1 = tDerFun u := by
        have h2 := Dfun_succ u 0
        rw [Dfun_zero] at h2
        simpa using h2
      rw [h1]
      exact hpdeS p hp
    | succ k ih =>
      intro p hp
      have h1 : Dfun u (k + 2) = tDerFun (Dfun u (k + 1)) := by
        simpa using Dfun_succ u (k + 1)
      rw [h1]
      have hev : (fun s : ℝ => Dfun u (k + 1) (s, p.2)) =ᶠ[nhds p.1]
          (fun s : ℝ => Aseq Φ u k (s, p.2)) := by
        have hmem : ((Set.Ioo σ T : Set ℝ) ×ˢ U) ∈ nhds p := hSopen.mem_nhds hp
        have htend : Tendsto (fun s : ℝ => (s, p.2)) (nhds p.1) (nhds p) := by
          rw [nhds_prod_eq]
          exact tendsto_id.prodMk tendsto_const_nhds
        filter_upwards [htend.eventually hmem] with s hs
        exact ih (s, p.2) hs
      rw [show tDerFun (Dfun u (k + 1)) p
          = deriv (fun s : ℝ => Dfun u (k + 1) (s, p.2)) p.1 from rfl, hev.deriv_eq]
      rfl
  have hPsiC : ∀ k : ℕ, ∀ p ∈ (Set.Ioo σ T : Set ℝ) ×ˢ U,
      Dfun u (k + 1) p = PsiC Φ k (p.2, fun i : Fin (k + 1) => cJet (Dfun u i) p) := by
    intro k p hp
    rw [hAseq k p hp]
    exact Aseq_eq_PsiC hΦ hSopen huS k p hp
  intro j
  induction j with
  | zero =>
    intro N
    choose Cb hCb using fun b : ℕ => hspat b
    refine ⟨max 1 ((kE E) ^ 2 * ∑ b ∈ Finset.range (max N 2 + 1), Cb b), ?_, ?_, ?_, ?_, ?_⟩
    · exact le_max_left _ _
    · intro i hi b hb t ht y hy
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst hi0
      have heq : (fun y' : E => Dfun u 0 (t, y')) = fun y' : E => u (t, y') := by
        funext y'; rw [Dfun_zero]
      rw [heq]
      have hmem : b ∈ Finset.range (max N 2 + 1) := Finset.mem_range.2 (by omega)
      have h1 : ‖iteratedFDeriv ℝ b (fun y' : E => u (t, y')) y‖
          ≤ ∑ b ∈ Finset.range (max N 2 + 1), Cb b :=
        le_trans ((hCb b).2 t (Set.Ioo_subset_Ico_self ht) y hy)
          (Finset.single_le_sum (fun b _ => (hCb b).1) hmem)
      refine le_trans h1 ?_
      have h0 : 0 ≤ ∑ b ∈ Finset.range (max N 2 + 1), Cb b :=
        Finset.sum_nonneg fun b _ => (hCb b).1
      exact le_trans (le_mul_of_one_le_left h0 (one_le_kE_sq (E := E))) (le_max_right _ _)
    · intro i hi t ht y hy
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst hi0
      have hsm : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => u (t, y')) y :=
        (huS.contDiffAt (hSopen.mem_nhds ⟨ht, hy⟩)).comp y
          (contDiffAt_const.prodMk contDiffAt_id)
      have hmem : ∀ b : ℕ, b ≤ 0 + 2 → b ∈ Finset.range (max N 2 + 1) :=
        fun b hb => Finset.mem_range.2 (by omega)
      have hbd : ∀ b ≤ 0 + 2,
          ‖iteratedFDeriv ℝ b (fun y' : E => u (t, y')) y‖
            ≤ ∑ b ∈ Finset.range (max N 2 + 1), Cb b :=
        fun b hb => le_trans ((hCb b).2 t (Set.Ioo_subset_Ico_self ht) y hy)
          (Finset.single_le_sum (fun b _ => (hCb b).1) (hmem b hb))
      have h0 : 0 ≤ ∑ b ∈ Finset.range (max N 2 + 1), Cb b :=
        Finset.sum_nonneg fun b _ => (hCb b).1
      have hC := norm_iteratedFDeriv_cJet1_le (h := fun y' : E => u (t, y')) (y := y) (a := 0)
        (M := ∑ b ∈ Finset.range (max N 2 + 1), Cb b) h0 hsm hbd
      rw [norm_iteratedFDeriv_zero] at hC
      have heq : (fun y' : E => Dfun u 0 (t, y')) = fun y' : E => u (t, y') := by
        funext y'; rw [Dfun_zero]
      simpa only [cJet_slice_eq, heq] using hC
    · intro i hi t ht
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst hi0
      have hslice : ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : E => u (t, y')) U :=
        contDiffOn_of_forall_contDiffAt hU fun y hy =>
          (huS.contDiffAt (hSopen.mem_nhds ⟨ht, hy⟩)).comp y
            (contDiffAt_const.prodMk contDiffAt_id)
      have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (cJet1 (fun y' : E => u (t, y'))) U :=
        contDiffOn_cJet1 hU hslice
      have hD0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : E => Dfun u 0 (t, y')) U := by
        simpa only [Dfun_zero] using hslice
      exact hD0
    · intro i hi t ht
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst hi0
      have hslice : ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : E => u (t, y')) U :=
        contDiffOn_of_forall_contDiffAt hU fun y hy =>
          (huS.contDiffAt (hSopen.mem_nhds ⟨ht, hy⟩)).comp y
            (contDiffAt_const.prodMk contDiffAt_id)
      have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (cJet1 (fun y' : E => u (t, y'))) U :=
        contDiffOn_cJet1 hU hslice
      have heq : (fun y' : E => Dfun u 0 (t, y')) = fun y' : E => u (t, y') := by
        funext y'; rw [Dfun_zero]
      refine h1.congr fun y' hy' => ?_
      rw [cJet_slice_eq, heq]
  | succ j ih =>
    intro N
    obtain ⟨M, hMinv⟩ := ih (max N 2 + 2)
    obtain ⟨hM1, hMslice, hMval, hMsliced, hMsm⟩ := hMinv
    have hD1 : 1 ≤ max 1 ((kE E) ^ 2 * M) := le_max_left _ _
    obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ y ∈ U, ‖y‖ ≤ R := by
      obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E)).1 hUb
      exact ⟨R, fun y hy => by
        have h := hR hy
        rwa [Metric.mem_closedBall, dist_zero_right] at h⟩
    have hPtbd : Bornology.IsBounded
        {z : E × (Fin (j + 1) → JetC (E := E)) |
          ∃ t ∈ Set.Ioo σ T, ∃ y ∈ U,
            z = (y, fun i : Fin (j + 1) => cJet (Dfun u i) (t, y))} := by
      refine (Metric.isBounded_iff_subset_closedBall
        (0 : E × (Fin (j + 1) → JetC (E := E)))).2 ⟨max (max R M) 0, ?_⟩
      rintro z ⟨t, ht, y, hy, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_mk]
      refine max_le ?_ ?_
      · exact le_trans (hR y hy) (le_trans (le_max_left _ _) (le_max_left _ _))
      · exact (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun i =>
          le_trans (hMval i.val (by omega) t ht y hy)
            (le_trans (le_max_right _ _) (le_max_left _ _))
    obtain ⟨Cψ, hCψ0, hCψ⟩ : ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ {z : E × (Fin (j + 1) → JetC (E := E)) |
            ∃ t ∈ Set.Ioo σ T, ∃ y ∈ U,
              z = (y, fun i : Fin (j + 1) => cJet (Dfun u i) (t, y))},
          ∀ b ≤ max N 2, ‖iteratedFDeriv ℝ b (PsiC Φ j) z‖ ≤ C := by
      choose Cb hCb using fun b : ℕ =>
        exists_bound_iteratedFDeriv_of_bounded_set (PsiC Φ j) (contDiff_PsiC hΦ j) hPtbd b
      refine ⟨∑ b ∈ Finset.range (max N 2 + 1), Cb b,
        Finset.sum_nonneg fun b _ => (hCb b).1, ?_⟩
      intro z hz b hb
      exact le_trans ((hCb b).2 z hz)
        (Finset.single_le_sum (fun b _ => (hCb b).1) (Finset.mem_range.2 (by omega)))
    have hident : ∀ t ∈ Set.Ioo σ T, ∀ y ∈ U,
        (fun y' : E => Dfun u (j + 1) (t, y')) =ᶠ[nhds y]
          (fun y' : E => PsiC Φ j (y', fun i : Fin (j + 1) => cJet (Dfun u i) (t, y'))) := by
      intro t ht y hy
      filter_upwards [hU.mem_nhds hy] with y' hy'
      exact hPsiC j (t, y') ⟨ht, hy'⟩
    have hbnd : ∀ t ∈ Set.Ioo σ T, ∀ y ∈ U, ∀ b ≤ max N 2,
        ‖iteratedFDeriv ℝ b (fun y' : E => Dfun u (j + 1) (t, y')) y‖ ≤
          (max N 2).factorial * Cψ * (max 1 ((kE E) ^ 2 * M)) ^ (max N 2) := by
      intro t ht y hy b hb
      have hFt : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun y' : E => (y', fun i : Fin (j + 1) => cJet (Dfun u i) (t, y'))) U :=
        contDiffOn_of_forall_contDiffAt hU fun y' hy' =>
          ContDiffAt.prodMk contDiffAt_id
            (contDiffAt_pi' fun (i : Fin (j + 1)) =>
              (hMsm i.val (by omega) t ht).contDiffAt (hU.mem_nhds hy'))
      have hD : ∀ i : ℕ, 1 ≤ i → i ≤ b → ‖iteratedFDerivWithin ℝ i
          (fun y' : E => (y', fun i : Fin (j + 1) => cJet (Dfun u i) (t, y'))) U y‖
            ≤ (max 1 ((kE E) ^ 2 * M)) ^ i := by
        intro i hi hib
        rw [iteratedFDerivWithin_of_isOpen i hU hy]
        have hci1 : ‖iteratedFDeriv ℝ i (fun y' : E => y') y‖ ≤ max 1 ((kE E) ^ 2 * M) :=
          le_trans (norm_iteratedFDeriv_self_le y i hi) hD1
        have hci2 : ‖iteratedFDeriv ℝ i (fun y' : E => fun k : Fin (j + 1) =>
            cJet (Dfun u k) (t, y')) y‖ ≤ max 1 ((kE E) ^ 2 * M) := by
          have hpi := JetsAux.norm_iteratedFDeriv_pi_le (C := max 1 ((kE E) ^ 2 * M))
            (fun k : Fin (j + 1) => fun y' : E => cJet (Dfun u k) (t, y')) y i
            (fun k => (hMsm k.val (by omega) t ht).contDiffAt (hU.mem_nhds hy))
            (fun k => by
              have hbdk : ∀ bb ≤ i + 2,
                  ‖iteratedFDeriv ℝ bb (fun y' : E => Dfun u k.val (t, y')) y‖ ≤ M :=
                fun bb hbb => hMslice k.val (by omega) bb (by omega) t ht y hy
              have hsmk : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Dfun u k.val (t, y')) y :=
                (hMsliced k.val (by omega) t ht).contDiffAt (hU.mem_nhds hy)
              have h := norm_iteratedFDeriv_cJet1_le (h := fun y' : E => Dfun u k.val (t, y'))
                (y := y) (a := i) (M := M) (le_trans zero_le_one hM1) hsmk hbdk
              simpa only [cJet_slice_eq] using h)
          simpa only [max_eq_left (le_trans zero_le_one hD1)] using hpi
        have hpr := AuxL.norm_iteratedFDeriv_prod_le (C := (max 1 ((kE E) ^ 2 * M)) ^ i)
          (fun y' : E => y') (fun y' : E => fun k : Fin (j + 1) => cJet (Dfun u k) (t, y'))
          y i contDiffAt_id (contDiffAt_pi' fun (k : Fin (j + 1)) =>
            (hMsm k.val (by omega) t ht).contDiffAt (hU.mem_nhds hy))
          (le_trans hci1 (le_self_pow₀ hD1 (by omega)))
          (le_trans hci2 (le_self_pow₀ hD1 (by omega)))
        simpa only [max_eq_left (pow_nonneg (le_trans zero_le_one hD1) i)] using hpr
      have hCb2 : ∀ i ≤ b, ‖iteratedFDerivWithin ℝ i (PsiC Φ j) Set.univ
          (y, fun k : Fin (j + 1) => cJet (Dfun u k) (t, y))‖ ≤ Cψ := by
        intro i hib
        rw [iteratedFDerivWithin_univ]
        exact hCψ (y, fun k : Fin (j + 1) => cJet (Dfun u k) (t, y))
          ⟨t, ht, y, hy, rfl⟩ i (le_trans hib hb)
      have hcomp := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := PsiC Φ j)
        (f := fun y' : E => (y', fun i : Fin (j + 1) => cJet (Dfun u i) (t, y')))
        (s := U) (t := Set.univ) (x := y) (n := b) (N := (⊤ : ℕ∞))
        ((contDiff_PsiC hΦ j).contDiffOn) hFt
        (WithTop.coe_le_coe.mpr (le_top : ((b : ℕ) : ℕ∞) ≤ ⊤))
        uniqueDiffOn_univ hU.uniqueDiffOn (fun y' _ => trivial) hy hCb2 hD
      have heq : iteratedFDeriv ℝ b (fun y' : E => Dfun u (j + 1) (t, y')) y
          = iteratedFDeriv ℝ b (fun y' : E => PsiC Φ j (y',
              fun i : Fin (j + 1) => cJet (Dfun u i) (t, y'))) y :=
        ((hident t ht y hy).iteratedFDeriv ℝ b).eq_of_nhds
      rw [heq, ← iteratedFDerivWithin_of_isOpen b hU hy]
      refine le_trans hcomp ?_
      have hfac : (b.factorial : ℝ) ≤ ((max N 2).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_le (by omega)
      have hDle : (max 1 ((kE E) ^ 2 * M)) ^ b ≤ (max 1 ((kE E) ^ 2 * M)) ^ (max N 2) :=
        pow_le_pow_right₀ hD1 (by omega)
      have hstep1 : (b.factorial : ℝ) * Cψ ≤ ((max N 2).factorial : ℝ) * Cψ :=
        mul_le_mul_of_nonneg_right hfac hCψ0
      exact mul_le_mul hstep1 hDle (by positivity) (by positivity)
    refine ⟨max M (max 1 ((kE E) ^ 2 * ((max N 2).factorial * Cψ *
      (max 1 ((kE E) ^ 2 * M)) ^ (max N 2)))), ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · intro i hi b hb t ht y hy
      rcases lt_or_eq_of_le hi with hlt | heq
      · exact le_trans (hMslice i (by omega) b (by omega) t ht y hy) (le_max_left _ _)
      · subst heq
        refine le_trans (hbnd t ht y hy b (by omega)) ?_
        have hA0 : (0 : ℝ) ≤ (max N 2).factorial * Cψ * (max 1 ((kE E) ^ 2 * M)) ^ (max N 2) :=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCψ0)
            (pow_nonneg (le_trans zero_le_one hD1) _)
        exact le_trans (le_mul_of_one_le_left hA0 (one_le_kE_sq (E := E)))
          (le_trans (le_max_right _ _) (le_max_right _ _))
    · intro i hi t ht y hy
      rcases lt_or_eq_of_le hi with hlt | heq
      · exact le_trans (hMval i (by omega) t ht y hy) (le_max_left _ _)
      · subst heq
        have hcomp_sm : ContDiffOn ℝ (⊤ : ℕ∞)
            (fun y' : E => PsiC Φ j (y', fun i : Fin (j + 1) => cJet (Dfun u i) (t, y'))) U :=
          contDiffOn_of_forall_contDiffAt hU fun y' hy' =>
            ContDiffAt.comp y' ((contDiff_PsiC hΦ j).contDiffAt)
              (ContDiffAt.prodMk contDiffAt_id
                (contDiffAt_pi' fun (i : Fin (j + 1)) =>
                  (hMsm i.val (by omega) t ht).contDiffAt (hU.mem_nhds hy')))
        have hslice_sm : ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : E => Dfun u (j + 1) (t, y')) U :=
          hcomp_sm.congr fun y' hy' => hPsiC j (t, y') ⟨ht, hy'⟩
        have hA0 : (0 : ℝ) ≤ (max N 2).factorial * Cψ * (max 1 ((kE E) ^ 2 * M)) ^ (max N 2) :=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCψ0)
            (pow_nonneg (le_trans zero_le_one hD1) _)
        have hCv := norm_iteratedFDeriv_cJet1_le (h := fun y' : E => Dfun u (j + 1) (t, y'))
          (y := y) (a := 0)
          (M := (max N 2).factorial * Cψ * (max 1 ((kE E) ^ 2 * M)) ^ (max N 2))
          hA0 (hslice_sm.contDiffAt (hU.mem_nhds hy))
          (fun b hb' => hbnd t ht y hy b (by omega))
        rw [norm_iteratedFDeriv_zero] at hCv
        rw [cJet_slice_eq]
        exact le_trans hCv (le_max_right _ _)
    · intro i hi t ht
      rcases lt_or_eq_of_le hi with hlt | heq
      · exact hMsliced i (by omega) t ht
      · subst heq
        have hcomp_sm : ContDiffOn ℝ (⊤ : ℕ∞)
            (fun y' : E => PsiC Φ j (y', fun i : Fin (j + 1) => cJet (Dfun u i) (t, y'))) U :=
          contDiffOn_of_forall_contDiffAt hU fun y' hy' =>
            ContDiffAt.comp y' ((contDiff_PsiC hΦ j).contDiffAt)
              (ContDiffAt.prodMk contDiffAt_id
                (contDiffAt_pi' fun (i : Fin (j + 1)) =>
                  (hMsm i.val (by omega) t ht).contDiffAt (hU.mem_nhds hy')))
        exact hcomp_sm.congr fun y' hy' => hPsiC j (t, y') ⟨ht, hy'⟩
    · intro i hi t ht
      rcases lt_or_eq_of_le hi with hlt | heq
      · exact hMsm i (by omega) t ht
      · subst heq
        have hcomp_sm : ContDiffOn ℝ (⊤ : ℕ∞)
            (fun y' : E => PsiC Φ j (y', fun i : Fin (j + 1) => cJet (Dfun u i) (t, y'))) U :=
          contDiffOn_of_forall_contDiffAt hU fun y' hy' =>
            ContDiffAt.comp y' ((contDiff_PsiC hΦ j).contDiffAt)
              (ContDiffAt.prodMk contDiffAt_id
                (contDiffAt_pi' fun (i : Fin (j + 1)) =>
                  (hMsm i.val (by omega) t ht).contDiffAt (hU.mem_nhds hy')))
        have hslice_sm : ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : E => Dfun u (j + 1) (t, y')) U :=
          hcomp_sm.congr fun y' hy' => hPsiC j (t, y') ⟨ht, hy'⟩
        have h1 := contDiffOn_cJet1 hU hslice_sm
        refine h1.congr fun y' hy' => ?_
        rw [cJet_slice_eq]

/-- All ambient iterated Fréchet derivatives of `u` are bounded on the open slab. -/

theorem interior_jets_bounded {σ T : ℝ} (hσT : σ < T) {U : Set E} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {u : ℝ × E → MatE (E := E)}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (Set.Ico σ T ×ˢ U))
    (hspat : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ U,
        ‖iteratedFDeriv ℝ k (fun y' : E => u (t, y')) y‖ ≤ C)
    {Φ : E × JetC (E := E) → MatE (E := E)} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hpde : ∀ p ∈ (Set.Ico σ T) ×ˢ U, deriv (fun s : ℝ => u (s, p.2)) p.1 =
        Φ (p.2, sJetData u p)) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ (Set.Ioo σ T) ×ˢ U,
        ‖iteratedFDeriv ℝ k u p‖ ≤ C := by
  intro k
  obtain ⟨M, hM⟩ := jets_inv hσT hU hUb hu hspat hΦ hpde k k
  obtain ⟨hM1, hMslice, hMval, hMsliced, hMsm⟩ := hM
  obtain ⟨Cm, hCm0, hCmL⟩ := AuxL.norm_iteratedFDeriv_le_mixed_timeDeriv (E := E) k
  refine ⟨Cm * ((k + 1 : ℕ) * M), mul_nonneg hCm0 (by positivity), fun p hp => ?_⟩
  have hSopen : IsOpen ((Set.Ioo σ T : Set ℝ) ×ˢ U) := isOpen_Ioo.prod hU
  have huS : ContDiffOn ℝ (⊤ : ℕ∞) u ((Set.Ioo σ T : Set ℝ) ×ˢ U) :=
    hu.mono (Set.prod_mono Set.Ioo_subset_Ico_self (subset_refl U))
  have h1 := hCmL u p (huS.contDiffAt (hSopen.mem_nhds hp))
  have h2 : ∑ j ∈ Finset.range (k + 1),
      ‖iteratedFDeriv ℝ (k - j) (fun y : E => Dfun u j (p.1, y)) p.2‖ ≤ (k + 1 : ℕ) * M := by
    have hsum : ∀ j ∈ Finset.range (k + 1),
        ‖iteratedFDeriv ℝ (k - j) (fun y : E => Dfun u j (p.1, y)) p.2‖ ≤ M := by
      intro j hj
      exact hMslice j (by simp only [Finset.mem_range] at hj; omega) (k - j) (by omega)
        p.1 hp.1 p.2 hp.2
    calc ∑ j ∈ Finset.range (k + 1),
          ‖iteratedFDeriv ℝ (k - j) (fun y : E => Dfun u j (p.1, y)) p.2‖
        ≤ ∑ _j ∈ Finset.range (k + 1), M := Finset.sum_le_sum hsum
      _ = (k + 1 : ℕ) * M := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hCm0)

theorem jets_bounded_of_pde
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {σ T : ℝ} (hσT : σ < T) {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {u : ℝ × E → Work.Diff.EXT.MatE (E := E)}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u ((Set.Ico σ T) ×ˢ U))
    (hspat : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ U,
        ‖iteratedFDeriv ℝ k (fun y' : E => u (t, y')) y‖ ≤ C)
    (hell : ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ U,
        ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        ε * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * u (t, y) i j)
    {Φ : E × (Work.Diff.EXT.MatE (E := E) ×
        (Fin (Module.finrank ℝ E) → Work.Diff.EXT.MatE (E := E)) ×
        (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Work.Diff.EXT.MatE (E := E))) →
        Work.Diff.EXT.MatE (E := E)}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hpde : ∀ p ∈ (Set.Ico σ T) ×ˢ U, deriv (fun s : ℝ => u (s, p.2)) p.1 =
        Φ (p.2, Work.Diff.EXT.sJetData u p)) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ (Set.Ico σ T) ×ˢ U,
        ‖iteratedFDeriv ℝ k u p‖ ≤ C := by
  intro k
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    obtain ⟨C, hC0, hC⟩ := hspat 0
    exact ⟨C, hC0, fun p hp => by simpa using hC p.1 hp.1 p.2 hp.2⟩
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨Cint, hCint0, hCint⟩ :=
      interior_jets_bounded hσT hU hUb hu hspat hΦ hpde (k' + 1)
    refine ⟨max (3 * Cint) Cint,
      le_trans hCint0 (le_max_right (3 * Cint) Cint), fun p hp => ?_⟩
    rcases lt_or_eq_of_le hp.1.1 with hlt | heq
    · exact le_trans (hCint p ⟨⟨hlt, hp.1.2⟩, hp.2⟩) (le_max_right _ _)
    · have hSopen : IsOpen ((Set.Ioo σ T : Set ℝ) ×ˢ U) := isOpen_Ioo.prod hU
      have huS : ContDiffOn ℝ (⊤ : ℕ∞) u ((Set.Ioo σ T : Set ℝ) ×ˢ U) :=
        hu.mono (Set.prod_mono Set.Ioo_subset_Ico_self (subset_refl U))
      have hdiff : DifferentiableOn ℝ (iteratedFDeriv ℝ k' u) ((Set.Ioo σ T : Set ℝ) ×ˢ U) := by
        have hw := huS.differentiableOn_iteratedFDerivWithin (m := k')
          (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top k')) hSopen.uniqueDiffOn
        exact hw.congr fun x hx => (iteratedFDerivWithin_of_isOpen k' hSopen hx).symm
      have hbd : ∀ q ∈ (Set.Ioo σ T : Set ℝ) ×ˢ U,
          ‖fderiv ℝ (iteratedFDeriv ℝ k' u) q‖ ≤ Cint := by
        intro q hq
        rw [norm_fderiv_iteratedFDeriv]
        exact hCint q hq
      have htr := AuxL.norm_fderiv_leftEndpoint_le (y₀ := p.2) hσT
        (hU.mem_nhds hp.2) hCint0 hdiff hbd
      have hpσ : p = (σ, p.2) := Prod.ext heq.symm rfl
      rw [hpσ, ← norm_fderiv_iteratedFDeriv]
      exact le_trans htr (le_max_left _ _)

end Jets2

end Work.Diff.EXT
