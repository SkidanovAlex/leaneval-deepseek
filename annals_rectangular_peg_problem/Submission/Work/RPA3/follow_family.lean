import Mathlib
import Submission.Work.RPA3.Defs
import Submission.Work.RPA3.Symp
import Submission.Work.RPA3.exists_flow_lipschitz
import Submission.Work.RPA3.lagrangian_orthogonal
import Submission.Work.RPA3.theta_per
import Submission.Work.RPA3.follow_family_defs
import Submission.Work.RPA3.Ycoef_spec
import Submission.Work.RPA3.Yfield_contDiff
import Submission.Work.RPA3.Yfield_bounded
import Submission.Work.RPA3.fderiv_Efun_apply
import Submission.Work.RPA3.Zfield_lipschitz
import Submission.Work.RPA3.exists_flow_lipschitz_general

open scoped ContDiff Topology

namespace Work.RPA3

/-- D3, follow the family.  Let H be a C⁴ Hamiltonian whose vector field is bounded and jointly
Lipschitz in (t,y) and whose directional derivatives along the family satisfy, for τ ∈ [0,1],
dH(∂_xℓ) = -ω(∂_τℓ, ∂_xℓ) and dH(∂_tℓ) = -ω(∂_τℓ, ∂_tℓ).  Then some global flow Φ of H
(IsFlow H Φ) carries the zero section onto the family at τ = 1: every z ∈ Zsec satisfies
Φ 1 z = ℓ 1 (x,t) for suitable x,t.

The C⁴ hypothesis is needed to rule out the loophole that `fderiv ℝ` is zero at points where H is not
differentiable, so that without it the hypotheses `hLip`, `hbdd`, `hgen` are satisfiable by a
discontinuous H whose vector field vanishes (a machine-checked counterexample is in
Submission/Work/RPA3/_ce_exists_flow_following.lean), and the conclusion then fails.  This is the
corrected form of the earlier statement `exists_flow_following`.

Proof.  (1) exists_flow_lipschitz gives a global flow Φ of the time-dependent field
V t y = hamVF (H t) y, with IsFlow H Φ (the field is bounded and jointly Lipschitz).
(2) Tangential correction: from the two generation identities and the differentiability of H (C⁴),
the vector W := X_H(ℓ τ (x,t)) - ∂_τℓ(τ,x,t) is ω-orthogonal to ∂_xℓ and to ∂_tℓ (using
symp (hamVF H x) v = -dH(v)); the plane spanned by those two vectors is Lagrangian (L.imm, L.lag), so
W lies in it (lagrangian_orthogonal).  The coefficients Y(τ,x,t) are smooth: they are the inverse of
the Gram matrix of (∂_xℓ, ∂_tℓ) applied to the pairings of W with ∂_xℓ, ∂_tℓ.  Y is 2π-periodic in t
and locally bounded and Lipschitz.
(3) Let Ψ be a global flow of the time-dependent vector field Y on the (x,t)-plane, obtained from the
two-dimensional analogue of exists_flow_lipschitz.
(4) ODE comparison on [0,1]: τ ↦ Φ τ (ℓ 0 (x,t)) and τ ↦ ℓ τ (Ψ τ (x,t)) are both integral curves of
the same time-dependent field V (for the second, the chain rule gives ∂_τℓ + dℓ(Y) = X_H ∘ ℓ by step
(2), using theta_per for the periodicity in the angle), with the same value at τ = 0 (Φ 0 = id); the
field is Lipschitz in the space variable by hypothesis, so ODE_solution_unique_of_mem_Icc_right gives
equality on [0,1].
(5) For z ∈ Zsec, L.start_surj gives z = ℓ 0 (x,t), so Φ 1 z = ℓ 1 (Ψ 1 (x,t)). -/
theorem follow_family (L : Work.RPA3.LagFamilyAll) (H : ℝ → Work.RPA3.PS → ℝ)
    (hH : ContDiff ℝ 4 (fun z : ℝ × Work.RPA3.PS => H z.1 z.2))
    (hLip : ∃ K : NNReal, LipschitzWith K (fun p : ℝ × Work.RPA3.PS => Work.RPA3.hamVF (H p.1) p.2))
    (hbdd : ∃ M : ℝ, ∀ t x, ‖Work.RPA3.hamVF (H t) x‖ ≤ M)
    (hgen : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x t,
      deriv (fun s => H τ (L.ℓ τ (x + s, t))) 0 =
        -Work.RPA3.symp (deriv (fun σ => L.ℓ σ (x, t)) τ) (deriv (fun y => L.ℓ τ (y, t)) x) ∧
      deriv (fun s => H τ (L.ℓ τ (x, t + s))) 0 =
        -Work.RPA3.symp (deriv (fun σ => L.ℓ σ (x, t)) τ) (deriv (fun s => L.ℓ τ (x, s)) t)) :
    ∃ Φ : ℝ → Work.RPA3.PS → Work.RPA3.PS, Work.RPA3.IsFlow H Φ ∧
      ∀ z ∈ Work.RPA3.Zsec, ∃ x t, Φ 1 z = L.ℓ 1 (x, t) := by
  classical
  -- (1) the global flow of the Hamiltonian
  obtain ⟨K, hK⟩ := hLip
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨Φ, hΦ0, hΦderiv⟩ := exists_flow_lipschitz (fun t y => hamVF (H t) y) K hK M hM
  have hIsFlow : IsFlow H Φ := ⟨hΦ0, hΦderiv⟩
  -- (2) smoothness and boundedness of the tangential correction field
  obtain ⟨MY, hMY⟩ := Yfield_bounded L H hH ⟨M, hM⟩
  have hYcd : ContDiff ℝ 1 (fun z : ℝ × (ℝ × ℝ) => Yfield L H z.1 z.2) := Yfield_contDiff L H hH
  -- each time slice of the joint Lipschitz field is Lipschitz
  have hVlip : ∀ t : ℝ, LipschitzWith K (fun y : PS => hamVF (H t) y) := by
    intro t
    refine LipschitzWith.of_dist_le_mul fun y y' => ?_
    have h := hK.dist_le_mul (t, y) (t, y')
    rwa [dist_mk_const_fst] at h
  refine ⟨Φ, hIsFlow, ?_⟩
  intro z hz
  obtain ⟨x0, t0, hxt0⟩ := L.start_surj z hz
  set p : ℝ × ℝ := (x0, t0) with hp
  have hp_eq : L.ℓ 0 p = z := hxt0
  -- (3) the cut-off field and its global flow
  set MZ : ℝ := max MY 0 with hMZdef
  have hMZnn : 0 ≤ MZ := le_max_right _ _
  have hYbdd' : ∀ τ ∈ Set.Icc (-2 : ℝ) 3, ∀ q, ‖Yfield L H τ q‖ ≤ MZ :=
    fun τ hτ q => le_trans (hMY τ hτ q) (le_max_left _ _)
  set c : ℝ := 2 * (‖p‖ + MZ) ^ 2 + 2 with hcdef
  have hZbdd : ∀ t q, ‖Zfield L H c t q‖ ≤ MZ := by
    intro t q
    by_cases ht : t ∈ Set.Icc (-2 : ℝ) 3
    · have habs : |chi t * bump c q| ≤ 1 := by
        rw [abs_mul]
        have h1 : |chi t| ≤ 1 := abs_le.mpr ⟨by linarith [(chi_bounds t).1], (chi_bounds t).2⟩
        have h2 : |bump c q| ≤ 1 :=
          abs_le.mpr ⟨by linarith [(bump_bounds c q).1], (bump_bounds c q).2⟩
        calc |chi t| * |bump c q| ≤ 1 * 1 :=
              mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      rw [Zfield_apply]
      calc ‖(chi t * bump c q) • Yfield L H t q‖
          = |chi t * bump c q| * ‖Yfield L H t q‖ := norm_smul _ _
        _ ≤ 1 * ‖Yfield L H t q‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
        _ = ‖Yfield L H t q‖ := one_mul _
        _ ≤ MZ := hYbdd' t ht q
    · have hchi : chi t = 0 := by
        have ht' : t < -2 ∨ 3 < t := by
          simp only [Set.mem_Icc, not_and_or, not_le] at ht
          exact ht
        rcases ht' with h | h
        · exact chi_zero_left h.le
        · exact chi_zero_right h.le
      rw [Zfield_apply, hchi, zero_mul, zero_smul, norm_zero]
      exact hMZnn
  obtain ⟨Kz, hKz⟩ := Zfield_lipschitz L H c hYcd
  obtain ⟨Ψ, hΨ0, hΨderiv⟩ :=
    exists_flow_lipschitz_general (E := ℝ × ℝ) (V := Zfield L H c) Kz hKz MZ hZbdd
  -- the trajectory stays inside the region where the cut-offs are `1`
  have htraj : ∀ σ ∈ Set.Icc (0 : ℝ) 1, ‖Ψ σ p - p‖ ≤ MZ := by
    intro σ hσ
    have hmain : ‖Ψ σ p - p‖ ≤ MZ * σ := by
      have h := norm_image_sub_le_of_norm_deriv_right_le_segment
        (f := fun s : ℝ => Ψ s p) (f' := fun s : ℝ => Zfield L H c s (Ψ s p))
        (a := 0) (b := σ) (C := MZ)
        ((continuous_iff_continuousAt.mpr (fun s => (hΨderiv p s).continuousAt)).continuousOn)
        (fun x _ => (hΨderiv p x).hasDerivWithinAt)
        (fun x _ => hZbdd x (Ψ x p))
      have h2 := h σ (⟨hσ.1, le_rfl⟩ : σ ∈ Set.Icc (0 : ℝ) σ)
      rw [hΨ0 p, sub_zero] at h2
      exact h2
    calc ‖Ψ σ p - p‖ ≤ MZ * σ := hmain
      _ ≤ MZ * 1 := mul_le_mul_of_nonneg_left hσ.2 hMZnn
      _ = MZ := mul_one _
  have hbump1 : ∀ σ ∈ Set.Icc (0 : ℝ) 1, bump c (Ψ σ p) = 1 := by
    intro σ hσ
    apply bump_one
    have h1 : ‖Ψ σ p - p‖ ≤ MZ := htraj σ hσ
    have hq1 : |(Ψ σ p).1| ≤ ‖p‖ + MZ := by
      have h2 : |(Ψ σ p).1 - p.1| ≤ ‖Ψ σ p - p‖ := by
        have h3 := norm_fst_le (Ψ σ p - p)
        rw [Real.norm_eq_abs] at h3
        simpa using h3
      have h3 : |p.1| ≤ ‖p‖ := by
        have := norm_fst_le p
        rwa [Real.norm_eq_abs] at this
      calc |(Ψ σ p).1| = |((Ψ σ p).1 - p.1) + p.1| := by ring_nf
        _ ≤ |(Ψ σ p).1 - p.1| + |p.1| := abs_add_le _ _
        _ ≤ MZ + ‖p‖ := add_le_add (le_trans h2 h1) h3
        _ = ‖p‖ + MZ := by ring
    have hq2 : |(Ψ σ p).2| ≤ ‖p‖ + MZ := by
      have h2 : |(Ψ σ p).2 - p.2| ≤ ‖Ψ σ p - p‖ := by
        have h3 := norm_snd_le (Ψ σ p - p)
        rw [Real.norm_eq_abs] at h3
        simpa using h3
      have h3 : |p.2| ≤ ‖p‖ := by
        have := norm_snd_le p
        rwa [Real.norm_eq_abs] at this
      calc |(Ψ σ p).2| = |((Ψ σ p).2 - p.2) + p.2| := by ring_nf
        _ ≤ |(Ψ σ p).2 - p.2| + |p.2| := abs_add_le _ _
        _ ≤ MZ + ‖p‖ := add_le_add (le_trans h2 h1) h3
        _ = ‖p‖ + MZ := by ring
    have hq1sq : (Ψ σ p).1 ^ 2 ≤ (‖p‖ + MZ) ^ 2 := by
      rw [← sq_abs ((Ψ σ p).1)]
      exact pow_le_pow_left₀ (abs_nonneg _) hq1 2
    have hq2sq : (Ψ σ p).2 ^ 2 ≤ (‖p‖ + MZ) ^ 2 := by
      rw [← sq_abs ((Ψ σ p).2)]
      exact pow_le_pow_left₀ (abs_nonneg _) hq2 2
    have hsum : (Ψ σ p).1 ^ 2 + (Ψ σ p).2 ^ 2 ≤ 2 * (‖p‖ + MZ) ^ 2 := by linarith
    have hcle : c - 1 = 2 * (‖p‖ + MZ) ^ 2 + 1 := by rw [hcdef]; ring
    linarith [hsum, hcle]
  have hZeq : ∀ σ ∈ Set.Icc (0 : ℝ) 1, Zfield L H c σ (Ψ σ p) = Yfield L H σ (Ψ σ p) := by
    intro σ hσ
    exact Zfield_eq_Yfield L H c σ (Ψ σ p)
      (chi_one ⟨by linarith [hσ.1], by linarith [hσ.2]⟩) (hbump1 σ hσ)
  have hΨcont : Continuous (fun s : ℝ => Ψ s p) :=
    continuous_iff_continuousAt.mpr (fun s => (hΨderiv p s).continuousAt)
  -- (4) ODE comparison on [0,1]
  set f : ℝ → PS := fun σ => Φ σ z with hf
  set g : ℝ → PS := fun σ => L.ℓ σ (Ψ σ p) with hg
  have hf0 : f 0 = z := by rw [hf]; exact hΦ0 z
  have hg0 : g 0 = z := by
    rw [hg]
    show L.ℓ 0 (Ψ 0 p) = z
    rw [hΨ0 p, hp_eq]
  have hfg : f 0 = g 0 := by rw [hf0, hg0]
  have hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    rw [hf]
    exact (continuous_iff_continuousAt.mpr (fun s => (hΦderiv z s).continuousAt)).continuousOn
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    rw [hg]
    have heq : (fun σ : ℝ => L.ℓ σ (Ψ σ p)) = Efun L ∘ (fun s : ℝ => (s, Ψ s p)) := rfl
    rw [heq]
    exact (L.smooth.continuous.comp (continuous_id.prodMk hΨcont)).continuousOn
  have hf' : ∀ t ∈ Set.Ico (0 : ℝ) 1, HasDerivWithinAt f (hamVF (H t) (f t)) (Set.Ici t) t := by
    intro t ht
    rw [hf]
    exact (hΦderiv z t).hasDerivWithinAt
  have hg' : ∀ t ∈ Set.Ico (0 : ℝ) 1, HasDerivWithinAt g (hamVF (H t) (g t)) (Set.Ici t) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, le_of_lt ht.2⟩
    rw [hg]
    have hq : HasDerivAt (fun s : ℝ => Ψ s p) (Zfield L H c t (Ψ t p)) t := hΨderiv p t
    have hcp : HasDerivAt (fun s : ℝ => (s, Ψ s p)) ((1 : ℝ), Zfield L H c t (Ψ t p)) t :=
      (hasDerivAt_id t).prodMk hq
    have hEfun : HasFDerivAt (Efun L) (fderiv ℝ (Efun L) (t, Ψ t p)) (t, Ψ t p) :=
      ((L.smooth.differentiable (by norm_num)).differentiableAt).hasFDerivAt
    have hcomp := hEfun.comp_hasDerivAt t hcp
    have hval : fderiv ℝ (Efun L) (t, Ψ t p) ((1 : ℝ), Zfield L H c t (Ψ t p))
        = hamVF (H t) (L.ℓ t (Ψ t p)) := by
      rw [hZeq t htIcc, fderiv_Efun_apply L t (Ψ t p).1 (Ψ t p).2
        (Yfield L H t (Ψ t p)).1 (Yfield L H t (Ψ t p)).2]
      have hspec := Ycoef_spec L H hH hgen t htIcc (Ψ t p).1 (Ψ t p).2
      have key : (Yfield L H t (Ψ t p)).1 • dX L t (Ψ t p).1 (Ψ t p).2
          + (Yfield L H t (Ψ t p)).2 • dT L t (Ψ t p).1 (Ψ t p).2
          = Wvec L H t (Ψ t p).1 (Ψ t p).2 := hspec
      rw [add_assoc, key]
      simp only [Wvec]
      abel
    rw [hval] at hcomp
    exact hcomp.hasDerivWithinAt
  have huniq := ODE_solution_unique_of_mem_Icc_right
    (v := fun t y => hamVF (H t) y) (s := fun _ => Set.univ) (K := K)
    (f := f) (g := g) (a := 0) (b := 1)
    (fun t _ => (hVlip t).lipschitzOnWith) hf_cont hf'
    (fun t _ => Set.mem_univ _) hg_cont hg'
    (fun t _ => Set.mem_univ _) hfg
  have h1 : f 1 = g 1 := huniq (by norm_num)
  -- (5) conclude
  have hfinal : Φ 1 z = L.ℓ 1 (Ψ 1 p) := by
    have ha : f 1 = Φ 1 z := by rw [hf]
    have hb : g 1 = L.ℓ 1 (Ψ 1 p) := by rw [hg]
    rw [← ha, h1, hb]
  exact ⟨(Ψ 1 p).1, (Ψ 1 p).2, by simpa using hfinal⟩

end Work.RPA3
