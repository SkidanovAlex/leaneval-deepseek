import Mathlib
import Submission.Work.Smooth.SphereJordan.log_compl_cut
import Submission.Work.Smooth.SphereJordan.planeIndex
import Submission.Work.Smooth.SphereJordan.winding_loop_of_bounded_component
import Submission.Work.Smooth.JordanSeparation.phragmen_brouwer_of_square
import Submission.Work.Smooth.JordanSeparation.onePoint_locallyPathConnected

/-!
# Janiszewski's theorem on the Riemann sphere, from the winding crux

This file proves `Work.JordanSeparation.janiszewskiZeroInftyOfWinding`: if `A₁, A₂` are closed
subsets of the Riemann sphere `OnePoint ℂ` with `A₁ ∩ A₂` nonempty and preconnected, neither of
which separates `0` from `∞`, then `A₁ ∪ A₂` does not separate `0` from `∞` either.

The proof follows Luisto's proof of Janiszewski's theorem (*Proof of the Jordan curve theorem*,
Lemma 2.4): choose paths `γ₁`, `γ₂` from `0` to `∞` avoiding `A₁` resp. `A₂`; there are continuous
logarithms `φ₁`, `φ₂` of the identity on the complements of their traces
(`Work.Smooth.SphereJordan.log_compl_cut`); on the complementary domain `F` containing the (finite
part of the) connected set `A₁ ∩ A₂` these logarithms differ by an integer multiple of `2 π I`, so
`φ₂` may be adjusted to agree with `φ₁` on `F`.  Their branches then glue to a continuous logarithm
`φ` on a neighbourhood `H` of `A₁ ∪ A₂`.  If `A₁ ∪ A₂` separated `0` from `∞`, the winding crux
`hcrux` (in the open-set form `loopIn_open_of_crux`) would produce a closed loop in `H` of non-zero
index about `0`; but `φ` is a continuous logarithm on `H`, so such a loop has index `0`
(`falseOfLoopWithLog`) — a contradiction.
-/

open Set Filter
open scoped OnePoint Topology

namespace Work.JordanSeparation

noncomputable section

/-! ## Elementary helpers -/

/-- The finite part of a closed subset of the Riemann sphere that avoids `∞` is a compact subset
of `ℂ`. -/
private theorem finitePart_isCompact {A : Set (OnePoint ℂ)} (hA : IsClosed A)
    (hinf : (OnePoint.infty : OnePoint ℂ) ∉ A) :
    IsCompact {z : ℂ | ((z : ℂ) : OnePoint ℂ) ∈ A} :=
  ((OnePoint.isClosed_iff_of_notMem hinf).mp hA).2

/-- Two disjoint compact subsets `E₁`, `E₂` of `ℂ` contained in open sets `S₁`, `S₂` respectively
admit disjoint open neighbourhoods `V₁ ⊇ E₁`, `V₂ ⊇ E₂` with `V₁ ⊆ S₁` and `V₂ ⊆ S₂`. -/
private theorem exists_disjoint_thickenings {E₁ E₂ S₁ S₂ : Set ℂ} (hE₁ : IsCompact E₁)
    (hE₂ : IsCompact E₂) (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂) (h₁ : E₁ ⊆ S₁) (h₂ : E₂ ⊆ S₂)
    (hd : Disjoint E₁ E₂) :
    ∃ V₁ V₂ : Set ℂ, IsOpen V₁ ∧ IsOpen V₂ ∧ E₁ ⊆ V₁ ∧ E₂ ⊆ V₂ ∧ V₁ ⊆ S₁ ∧ V₂ ⊆ S₂ ∧
      Disjoint V₁ V₂ := by
  obtain ⟨U₁, U₂, hU₁o, hU₂o, hE₁U₁, hE₂U₂, hdisj⟩ :=
    SeparatedNhds.of_isCompact_isCompact hE₁ hE₂ hd
  exact ⟨U₁ ∩ S₁, U₂ ∩ S₂, hU₁o.inter hS₁, hU₂o.inter hS₂,
    fun z hz => ⟨hE₁U₁ hz, h₁ hz⟩, fun z hz => ⟨hE₂U₂ hz, h₂ hz⟩,
    inter_subset_right, inter_subset_right, hdisj.mono inter_subset_left inter_subset_left⟩

/-- A closed loop lying in a set `H` carrying a continuous logarithm `φ` of the identity
(`Complex.exp (φ z) = z` for `z ∈ H`) has index `0` about the origin. -/
private theorem falseOfLoopWithLog {H : Set ℂ} {φ : ℂ → ℂ} (hφc : ContinuousOn φ H)
    (hφ : ∀ z ∈ H, Complex.exp (φ z) = z) {c : C(unitInterval, ℂ)} (hcH : ∀ t, c t ∈ H)
    (hloop : c 0 = c 1) (hidx : Work.Smooth.SphereJordan.loopIndex c ≠ 0) : False := by
  have hne : ∀ t, c t ≠ 0 := by
    intro t h0
    exact Complex.exp_ne_zero (φ (c t)) ((hφ (c t) (hcH t)).trans h0)
  set Λ : C(unitInterval, ℂ) :=
    ⟨fun t => φ (c t), hφc.comp_continuous c.continuous hcH⟩ with hΛ
  have hΛe : ∀ t, Complex.exp (Λ t) = c t := fun t => hφ (c t) (hcH t)
  have hfix : Λ 1 = Λ 0 := by
    simp only [hΛ, ContinuousMap.coe_mk]
    rw [hloop]
  exact hidx (Work.Smooth.SphereJordan.loopIndex_eq_zero_of_lift c hne hloop Λ hΛe hfix)

/-- Integer multiples of `2 π I` are `2 π`-separated: if a difference of two such is shorter
than `π`, the multipliers agree. -/
private lemma int_eq_of_norm_mul_lt_pi {m n : ℤ}
    (h : ‖(((m : ℂ) - (n : ℂ)) * (2 * ↑Real.pi * Complex.I))‖ < Real.pi) : m = n := by
  by_contra hne
  have hmn : m - n ≠ 0 := sub_ne_zero.mpr hne
  have h1 : (1 : ℝ) ≤ |((m - n : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hmn
  have h2 : ‖((m : ℂ) - (n : ℂ))‖ = |((m - n : ℤ) : ℝ)| := by
    rw [← Int.cast_sub, Complex.norm_intCast]
  have h3 : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  rw [norm_mul, h2, h3] at h
  nlinarith [Real.pi_pos]

/-- Two continuous logarithms of the identity on a preconnected set differ by a constant integer
multiple of `2 π I`. -/
private theorem exists_int_of_log_diff {Ω F : Set ℂ} (hFΩ : F ⊆ Ω) (hFpre : IsPreconnected F)
    {φ ψ : ℂ → ℂ} (hφc : ContinuousOn φ Ω) (hψc : ContinuousOn ψ Ω)
    (hφ : ∀ z ∈ Ω, Complex.exp (φ z) = z) (hψ : ∀ z ∈ Ω, Complex.exp (ψ z) = z) :
    ∃ k : ℤ, ∀ z ∈ F, φ z - ψ z = (k : ℂ) * (2 * ↑Real.pi * Complex.I) := by
  have hne : ∀ z ∈ Ω, z ≠ 0 := fun z hz h => Complex.exp_ne_zero (φ z) ((hφ z hz).trans h)
  have hexp1 : ∀ z ∈ Ω, Complex.exp (φ z - ψ z) = 1 := fun z hz => by
    rw [Complex.exp_sub, hφ z hz, hψ z hz, div_self (hne z hz)]
  rcases F.eq_empty_or_nonempty with hF | hF
  · exact ⟨0, fun z hz => absurd (hF ▸ hz) (Set.notMem_empty z)⟩
  · obtain ⟨z₀, hz₀⟩ := hF
    obtain ⟨k₀, hk₀⟩ := Complex.exp_eq_one_iff.mp (hexp1 z₀ (hFΩ hz₀))
    refine ⟨k₀, fun z hz => ?_⟩
    have key : ∀ z ∈ F, φ z - ψ z = φ z₀ - ψ z₀ := by
      have hloc : IsLocallyConstant (fun z : ↥F => φ z - ψ z) := by
        rw [IsLocallyConstant.iff_eventually_eq]
        intro z
        have hzΩ : (z : ℂ) ∈ Ω := hFΩ z.2
        obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp (hexp1 (z : ℂ) hzΩ)
        have hcont : ContinuousOn (fun w => φ w - ψ w) F := (hφc.mono hFΩ).sub (hψc.mono hFΩ)
        have hcwa : ContinuousWithinAt (fun w => φ w - ψ w) F ((z:ℂ)) :=
          hcont.continuousWithinAt z.2
        obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuousWithinAt_iff.mp hcwa) Real.pi Real.pi_pos
        have hmem : Subtype.val ⁻¹' (Metric.ball ((z : ↥F) : ℂ) δ) ∈ 𝓝 z := by
          refine IsOpen.mem_nhds (Metric.isOpen_ball.preimage continuous_subtype_val) ?_
          simp only [Set.mem_preimage, Metric.mem_ball, dist_self]
          exact hδpos
        refine Filter.mem_of_superset hmem (fun w hw => ?_)
        have hlt : ‖(φ (w:ℂ) - ψ (w:ℂ)) - (φ (z:ℂ) - ψ (z:ℂ))‖ < Real.pi := by
          have h := hδ w.2 hw
          simpa [dist_eq_norm] using h
        obtain ⟨k', hk'⟩ := Complex.exp_eq_one_iff.mp (hexp1 (w:ℂ) (hFΩ w.2))
        have hkk : k' = k := by
          refine int_eq_of_norm_mul_lt_pi (n := k) ?_
          have hdiff : (φ (w:ℂ) - ψ (w:ℂ)) - (φ (z:ℂ) - ψ (z:ℂ)) =
              (((k' : ℂ) - (k : ℂ)) * (2 * ↑Real.pi * Complex.I)) := by
            rw [hk', hk]; ring
          rw [← hdiff]; exact hlt
        show φ (w:ℂ) - ψ (w:ℂ) = φ (z:ℂ) - ψ (z:ℂ)
        rw [hk', hk, hkk]
      have pre : PreconnectedSpace ↥F := isPreconnected_iff_preconnectedSpace.mp hFpre
      intro z hz
      exact hloc.apply_eq_of_preconnectedSpace ⟨z, hz⟩ ⟨z₀, hz₀⟩
    rw [key z hz, hk₀]

/-- The identity of `ℂ*` restricted to the complement of a path from `0` to `∞` has a logarithm. -/
private theorem exists_logOn_compl_path {γ : C(unitInterval, OnePoint ℂ)}
    (h0 : γ 0 = ((0 : ℂ) : OnePoint ℂ)) (h1 : γ 1 = OnePoint.infty) :
    ∃ F : ℂ → ℂ, ContinuousOn F {z : ℂ | ((z : ℂ) : OnePoint ℂ) ∈ (Set.range γ)ᶜ} ∧
      ∀ z : ℂ, ((z : ℂ) : OnePoint ℂ) ∈ (Set.range γ)ᶜ → Complex.exp (F z) = z := by
  classical
  obtain ⟨f, hfc, hfe⟩ := Work.Smooth.SphereJordan.log_compl_cut h0 h1
  refine ⟨fun z => if h : ((z : ℂ) : OnePoint ℂ) ∈ (Set.range γ)ᶜ then f ⟨z, h⟩ else 0, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have hcont : Continuous (fun z : ↥{z : ℂ | ((z : ℂ) : OnePoint ℂ) ∈ (Set.range γ)ᶜ} =>
        f ⟨z.1, z.2⟩) := hfc.comp (Continuous.subtype_mk continuous_subtype_val _)
    refine hcont.congr (fun z => ?_)
    simp only [Set.domRestrict_apply]
    split_ifs with h
    · exact congrArg f (Subtype.ext rfl)
    · exact absurd z.2 h
  · intro z hz
    simp only [dif_pos hz]
    exact hfe ⟨z, hz⟩

/-- The planar winding crux in the form needed below: if `H` is an open subset of the Riemann
sphere with `0 ∉ H` such that `H` separates `0` from `∞`, then `H` contains a closed loop of
non-zero index about `0`. -/
private theorem loopIn_open_of_crux
    (hcrux : ∀ {F : Set ℂ}, IsClosed F → (0 : ℂ) ∈ F →
      Bornology.IsBounded (connectedComponentIn F (0 : ℂ)) →
      ∃ c : C(unitInterval, ℂ), (∀ t, c t ∉ F) ∧ (∀ t, c t ≠ 0) ∧ c 0 = c 1 ∧
        Work.Smooth.SphereJordan.loopIndex c ≠ 0)
    {H : Set (OnePoint ℂ)} (hH : IsOpen H) (h0 : ((0 : ℂ) : OnePoint ℂ) ∉ H)
    (hinf : (OnePoint.infty : OnePoint ℂ) ∉ connectedComponentIn Hᶜ ((0 : ℂ) : OnePoint ℂ)) :
    ∃ c : C(unitInterval, ℂ), (∀ t, ((c t : ℂ) : OnePoint ℂ) ∈ H) ∧ (∀ t, c t ≠ 0) ∧
      c 0 = c 1 ∧ Work.Smooth.SphereJordan.loopIndex c ≠ 0 := by
  classical
  set K : Set (OnePoint ℂ) := Hᶜ with hK
  have hKcl : IsClosed K := hH.isClosed_compl
  set F : Set ℂ := {z : ℂ | ((z : ℂ) : OnePoint ℂ) ∈ K} with hF
  have h0K : ((0:ℂ) : OnePoint ℂ) ∈ K := by simp only [hK, Set.mem_compl_iff]; exact h0
  have h0F : (0 : ℂ) ∈ F := by simp only [hF, Set.mem_ofPred_eq]; exact h0K
  have hFcl : IsClosed F := hKcl.preimage OnePoint.continuous_coe
  have hcompK_closed : IsClosed (connectedComponentIn K ((0:ℂ) : OnePoint ℂ)) := by
    rw [connectedComponentIn_eq_image h0K]
    exact hKcl.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hcompK_compact : IsCompact (connectedComponentIn K ((0:ℂ) : OnePoint ℂ)) :=
    hcompK_closed.isCompact
  have hbound : ∃ R : ℝ, ∀ z : ℂ,
      ((z : ℂ) : OnePoint ℂ) ∈ connectedComponentIn K ((0:ℂ) : OnePoint ℂ) → ‖z‖ ≤ R := by
    have hopen : IsOpen (connectedComponentIn K ((0:ℂ) : OnePoint ℂ))ᶜ := hcompK_closed.isOpen_compl
    have hmem : (connectedComponentIn K ((0:ℂ) : OnePoint ℂ))ᶜ ∈ nhds (OnePoint.infty : OnePoint ℂ) :=
      hopen.mem_nhds hinf
    obtain ⟨C, ⟨-, hCcomp⟩, hCsub⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hmem
    obtain ⟨R, hR⟩ := hCcomp.isBounded.subset_closedBall (0 : ℂ)
    refine ⟨R, fun z hz => ?_⟩
    have hzC : z ∈ C := by
      by_contra hzc
      have h1 : ((z : ℂ) : OnePoint ℂ) ∈ OnePoint.some '' Cᶜ := ⟨z, hzc, rfl⟩
      exact (hCsub (Or.inl h1)) hz
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR hzC
  have hsubFK : connectedComponentIn F (0 : ℂ) ⊆
      {z : ℂ | ((z : ℂ) : OnePoint ℂ) ∈ connectedComponentIn K ((0:ℂ) : OnePoint ℂ)} := by
    intro z hz
    have hpre : IsPreconnected (OnePoint.some '' connectedComponentIn F (0 : ℂ)) :=
      isPreconnected_connectedComponentIn.image _ OnePoint.continuous_coe.continuousOn
    have hsub : OnePoint.some '' connectedComponentIn F (0 : ℂ) ⊆ K := by
      rintro _ ⟨w, hw, rfl⟩
      have hwF : w ∈ F := connectedComponentIn_subset F (0 : ℂ) hw
      simpa only [hF, Set.mem_ofPred_eq] using hwF
    exact hpre.subset_connectedComponentIn ⟨0, mem_connectedComponentIn h0F, rfl⟩ hsub ⟨z, hz, rfl⟩
  have hbdd : Bornology.IsBounded (connectedComponentIn F (0 : ℂ)) := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
    obtain ⟨R, hR⟩ := hbound
    exact ⟨R, fun z hz => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hR z (hsubFK hz)⟩
  obtain ⟨c, hcF, hcne, hloop, hidx⟩ := hcrux hFcl h0F hbdd
  refine ⟨c, ?_, hcne, hloop, hidx⟩
  intro t
  have h1 : ((c t : ℂ) : OnePoint ℂ) ∈ Kᶜ := by
    rw [Set.mem_compl_iff]
    intro hmem
    exact hcF t (by simpa only [hF, Set.mem_ofPred_eq] using hmem)
  simpa only [hK, compl_compl] using h1

/-! ## Janiszewski's theorem for the points `0` and `∞`, from the winding crux -/

theorem janiszewskiZeroInftyOfWinding (hcrux : ∀ {F : Set ℂ}, IsClosed F → (0 : ℂ) ∈ F → Bornology.IsBounded (connectedComponentIn F (0 : ℂ)) → ∃ c : C(unitInterval, ℂ), (∀ t, c t ∉ F) ∧ (∀ t, c t ≠ 0) ∧ c 0 = c 1 ∧ Work.Smooth.SphereJordan.loopIndex c ≠ 0) {A₁ A₂ : Set (OnePoint ℂ)} (h₁ : IsClosed A₁) (h₂ : IsClosed A₂) (hne : (A₁ ∩ A₂).Nonempty) (hcon : IsPreconnected (A₁ ∩ A₂)) (h0 : ((0 : ℂ) : OnePoint ℂ) ∉ A₁ ∪ A₂) (hinf : (OnePoint.infty : OnePoint ℂ) ∉ A₁ ∪ A₂) (h₁' : (OnePoint.infty : OnePoint ℂ) ∈ connectedComponentIn A₁ᶜ ((0 : ℂ) : OnePoint ℂ)) (h₂' : (OnePoint.infty : OnePoint ℂ) ∈ connectedComponentIn A₂ᶜ ((0 : ℂ) : OnePoint ℂ)) : (OnePoint.infty : OnePoint ℂ) ∈ connectedComponentIn (A₁ ∪ A₂)ᶜ ((0 : ℂ) : OnePoint ℂ) := by
  classical
  haveI : LocallyPathConnectedSpace (OnePoint ℂ) :=
    Work.Smooth.JordanSeparation.onePoint_locallyPathConnected
  by_contra hbad
  -- paths from `0` to `∞` avoiding `A₁` resp. `A₂`
  have h0A₁ : ((0 : ℂ) : OnePoint ℂ) ∈ A₁ᶜ := fun h => h0 (Or.inl h)
  have h0A₂ : ((0 : ℂ) : OnePoint ℂ) ∈ A₂ᶜ := fun h => h0 (Or.inr h)
  obtain ⟨γ₁, hγ₁⟩ :=
    Work.Smooth.JordanSeparation.joinedIn_of_mem_connectedComponentIn h₁.isOpen_compl h0A₁ h₁'
  obtain ⟨γ₂, hγ₂⟩ :=
    Work.Smooth.JordanSeparation.joinedIn_of_mem_connectedComponentIn h₂.isOpen_compl h0A₂ h₂'
  -- logarithms on the complements of the two traces
  obtain ⟨φ₁, hφ₁c, hφ₁e⟩ := exists_logOn_compl_path γ₁.source γ₁.target
  obtain ⟨φ₂, hφ₂c, hφ₂e⟩ := exists_logOn_compl_path γ₂.source γ₂.target
  set S₁ : Set ℂ :=
    {z : ℂ | ((z : ℂ) : OnePoint ℂ) ∈ (Set.range (γ₁ : C(unitInterval, OnePoint ℂ)))ᶜ} with hS₁
  set S₂ : Set ℂ :=
    {z : ℂ | ((z : ℂ) : OnePoint ℂ) ∈ (Set.range (γ₂ : C(unitInterval, OnePoint ℂ)))ᶜ} with hS₂
  have hγ₁C : ∀ t, (γ₁ : C(unitInterval, OnePoint ℂ)) t ∉ A₁ := fun t => hγ₁ t
  have hγ₂C : ∀ t, (γ₂ : C(unitInterval, OnePoint ℂ)) t ∉ A₂ := fun t => hγ₂ t
  have hφ₁cS : ContinuousOn φ₁ S₁ := by rw [hS₁]; exact hφ₁c
  have hφ₂cS : ContinuousOn φ₂ S₂ := by rw [hS₂]; exact hφ₂c
  have hφ₁eS : ∀ z ∈ S₁, Complex.exp (φ₁ z) = z := by rw [hS₁]; exact hφ₁e
  have hφ₂eS : ∀ z ∈ S₂, Complex.exp (φ₂ z) = z := by rw [hS₂]; exact hφ₂e
  have hS₁o : IsOpen S₁ := by
    rw [hS₁]
    exact (((isCompact_range (γ₁ : C(unitInterval, OnePoint ℂ)).continuous).isClosed.isOpen_compl).preimage
      OnePoint.continuous_coe)
  have hS₂o : IsOpen S₂ := by
    rw [hS₂]
    exact (((isCompact_range (γ₂ : C(unitInterval, OnePoint ℂ)).continuous).isClosed.isOpen_compl).preimage
      OnePoint.continuous_coe)
  -- the finite part of `A₁ ∩ A₂` lies in a single complementary domain of `|γ₁| ∪ |γ₂|`
  obtain ⟨k₀, hk₀⟩ := hne
  have hk₀ne : k₀ ≠ OnePoint.infty := fun h => hinf (by rw [← h]; exact Or.inl hk₀.1)
  obtain ⟨k₀', hk₀'⟩ := OnePoint.ne_infty_iff_exists.mp hk₀ne
  have hk₀'S₁ : k₀' ∈ S₁ := by
    simp only [hS₁, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_range, not_exists]
    intro t ht
    exact hγ₁C t (by rw [ht, hk₀']; exact hk₀.1)
  have hk₀'S₂ : k₀' ∈ S₂ := by
    simp only [hS₂, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_range, not_exists]
    intro t ht
    exact hγ₂C t (by rw [ht, hk₀']; exact hk₀.2)
  set F : Set ℂ := connectedComponentIn (S₁ ∩ S₂) k₀' with hF
  have hFopen : IsOpen F := by rw [hF]; exact (hS₁o.inter hS₂o).connectedComponentIn
  have hFpre : IsPreconnected F := by rw [hF]; exact isPreconnected_connectedComponentIn
  have hFsub : F ⊆ S₁ ∩ S₂ := by
    rw [hF]; exact connectedComponentIn_subset (S₁ ∩ S₂) k₀'
  -- the difference of the two logarithms is constant on `F`
  obtain ⟨k, hk⟩ := exists_int_of_log_diff (Ω := S₁ ∩ S₂) (F := F) hFsub hFpre
    (hφ₁cS.mono inter_subset_left) (hφ₂cS.mono inter_subset_right)
    (fun z hz => hφ₁eS z hz.1) (fun z hz => hφ₂eS z hz.2)
  set φ₂' : ℂ → ℂ := fun z => φ₂ z + (k : ℂ) * (2 * ↑Real.pi * Complex.I) with hφ₂'
  have hφ₂'c : ContinuousOn φ₂' S₂ := by
    rw [hφ₂']; exact hφ₂cS.add continuousOn_const
  have hφ₂'e : ∀ z ∈ S₂, Complex.exp (φ₂' z) = z := by
    intro z hz
    have h1 : Complex.exp ((k : ℂ) * (2 * ↑Real.pi * Complex.I)) = 1 := by
      rw [Complex.exp_eq_one_iff]; exact ⟨k, rfl⟩
    simp only [hφ₂', Complex.exp_add, hφ₂eS z hz, h1, mul_one]
  have hagree : ∀ z ∈ F, φ₁ z = φ₂' z := by
    intro z hz
    have h2 := hk z hz
    simp only [hφ₂']
    rw [← h2]; ring
  -- disjoint neighbourhoods of the two pieces of `A₁ ∪ A₂`
  have hA₁' : IsCompact {z : ℂ | ((z : ℂ) : OnePoint ℂ) ∈ A₁} :=
    finitePart_isCompact h₁ (fun h => hinf (Or.inl h))
  have hA₂' : IsCompact {z : ℂ | ((z : ℂ) : OnePoint ℂ) ∈ A₂} :=
    finitePart_isCompact h₂ (fun h => hinf (Or.inr h))
  set E₁ : Set ℂ := {z : ℂ | ((z : ℂ) : OnePoint ℂ) ∈ A₁} ∩ Fᶜ with hE₁
  set E₂ : Set ℂ := {z : ℂ | ((z : ℂ) : OnePoint ℂ) ∈ A₂} ∩ Fᶜ with hE₂
  have hE₁c : IsCompact E₁ := by rw [hE₁]; exact hA₁'.inter_right hFopen.isClosed_compl
  have hE₂c : IsCompact E₂ := by rw [hE₂]; exact hA₂'.inter_right hFopen.isClosed_compl
  have hE₁S₁ : E₁ ⊆ S₁ := by
    rintro z ⟨hzA, -⟩
    simp only [hS₁, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_range, not_exists]
    intro t ht
    exact hγ₁C t (by rw [ht]; exact hzA)
  have hE₂S₂ : E₂ ⊆ S₂ := by
    rintro z ⟨hzA, -⟩
    simp only [hS₂, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_range, not_exists]
    intro t ht
    exact hγ₂C t (by rw [ht]; exact hzA)
  set K' : Set ℂ := OnePoint.some ⁻¹' (A₁ ∩ A₂) with hK'
  have hK'pre : IsPreconnected K' := by
    rw [hK']
    refine IsPreconnected.preimage_of_isOpenMap hcon OnePoint.coe_injective OnePoint.isOpenMap_coe ?_
    rintro x ⟨hxA₁, -⟩
    exact OnePoint.ne_infty_iff_exists.mp (fun h => hinf (by rw [← h]; exact Or.inl hxA₁))
  have hk₀'K : k₀' ∈ K' := by
    rw [hK']
    show OnePoint.some k₀' ∈ A₁ ∩ A₂
    rw [hk₀']
    exact hk₀
  have hK'Ω : K' ⊆ S₁ ∩ S₂ := by
    intro z hz
    rw [hK'] at hz
    refine ⟨?_, ?_⟩
    · simp only [hS₁, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_range, not_exists]
      intro t ht
      exact hγ₁C t (by rw [ht]; exact hz.1)
    · simp only [hS₂, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_range, not_exists]
      intro t ht
      exact hγ₂C t (by rw [ht]; exact hz.2)
  have hK'F : K' ⊆ F := by
    rw [hF]
    exact hK'pre.subset_connectedComponentIn hk₀'K hK'Ω
  have hEdisj : Disjoint E₁ E₂ := by
    rw [Set.disjoint_left]
    rintro z ⟨hzA₁, hzF⟩ ⟨hzA₂, -⟩
    exact hzF (hK'F (by rw [hK']; exact ⟨hzA₁, hzA₂⟩))
  obtain ⟨V₁, V₂, hV₁o, hV₂o, hE₁V₁, hE₂V₂, hV₁S₁, hV₂S₂, hVdisj⟩ :=
    exists_disjoint_thickenings hE₁c hE₂c hS₁o hS₂o hE₁S₁ hE₂S₂ hEdisj
  -- the glued logarithm on the neighbourhood `H = (V₁ ∪ F) ∪ (V₂ ∪ F)`
  set W₁ : Set ℂ := V₁ ∪ F with hW₁
  set W₂ : Set ℂ := V₂ ∪ F with hW₂
  have hW₁o : IsOpen W₁ := by rw [hW₁]; exact hV₁o.union hFopen
  have hW₂o : IsOpen W₂ := by rw [hW₂]; exact hV₂o.union hFopen
  set H : Set ℂ := W₁ ∪ W₂ with hH
  have hHo : IsOpen H := by rw [hH]; exact hW₁o.union hW₂o
  have hW₁W₂ : W₁ ∩ W₂ ⊆ F := by
    rintro z ⟨hz1, hz2⟩
    rw [hW₁] at hz1
    rw [hW₂] at hz2
    rcases hz1 with hz1 | hz1
    · rcases hz2 with hz2 | hz2
      · exact (Set.disjoint_left.mp hVdisj hz1 hz2).elim
      · exact hz2
    · exact hz1
  set φ : ℂ → ℂ := fun z => if z ∈ W₁ then φ₁ z else φ₂' z with hφ
  have hφW₁ : ∀ z ∈ W₁, φ z = φ₁ z := by
    intro z hz
    simp only [hφ]
    rw [if_pos hz]
  have hφW₂ : ∀ z ∈ W₂, φ z = φ₂' z := by
    intro z hz
    by_cases hz1 : z ∈ W₁
    · rw [hφW₁ z hz1]
      exact hagree z (hW₁W₂ ⟨hz1, hz⟩)
    · simp only [hφ]
      rw [if_neg hz1]
  have hφspec : ∀ z ∈ H, Complex.exp (φ z) = z := by
    intro z hz
    rw [hH] at hz
    rcases hz with hz | hz
    · rw [hφW₁ z hz]
      rw [hW₁] at hz
      rcases hz with hz | hz
      · exact hφ₁eS z (hV₁S₁ hz)
      · exact hφ₁eS z (hFsub hz).1
    · rw [hφW₂ z hz]
      rw [hW₂] at hz
      rcases hz with hz | hz
      · exact hφ₂'e z (hV₂S₂ hz)
      · exact hφ₂'e z (hFsub hz).2
  have hφcont : ContinuousOn φ H := by
    refine continuousOn_of_forall_continuousAt (fun z hz => ?_)
    rw [hH] at hz
    rcases hz with hz | hz
    · have hzS₁ : z ∈ S₁ := by
        rw [hW₁] at hz
        exact hz.elim (fun h => hV₁S₁ h) (fun h => (hFsub h).1)
      refine (hφ₁cS.continuousAt (hS₁o.mem_nhds hzS₁)).congr ?_
      exact Filter.eventually_of_mem (hW₁o.mem_nhds hz) (fun w hw => (hφW₁ w hw).symm)
    · have hzS₂ : z ∈ S₂ := by
        rw [hW₂] at hz
        exact hz.elim (fun h => hV₂S₂ h) (fun h => (hFsub h).2)
      refine (hφ₂'c.continuousAt (hS₂o.mem_nhds hzS₂)).congr ?_
      exact Filter.eventually_of_mem (hW₂o.mem_nhds hz) (fun w hw => (hφW₂ w hw).symm)
  -- the sphere-side bookkeeping
  set Hs : Set (OnePoint ℂ) := (fun z : ℂ => ((z : ℂ) : OnePoint ℂ)) '' H with hHs
  have hHso : IsOpen Hs := by rw [hHs]; exact OnePoint.isOpenMap_coe H hHo
  have h0H : (0 : ℂ) ∉ H := by
    intro h0H
    rw [hH] at h0H
    rcases h0H with hz | hz
    · rw [hW₁] at hz
      have hzS₁ : (0 : ℂ) ∈ S₁ :=
        hz.elim (fun h => hV₁S₁ h) (fun h => (hFsub h).1)
      simp only [hS₁, Set.mem_compl_iff] at hzS₁
      exact hzS₁ ⟨0, γ₁.source⟩
    · rw [hW₂] at hz
      have hzS₂ : (0 : ℂ) ∈ S₂ :=
        hz.elim (fun h => hV₂S₂ h) (fun h => (hFsub h).2)
      simp only [hS₂, Set.mem_compl_iff] at hzS₂
      exact hzS₂ ⟨0, γ₂.source⟩
  have hH0 : ((0 : ℂ) : OnePoint ℂ) ∉ Hs := by
    rw [hHs]
    rintro ⟨z, hz, hz0⟩
    exact h0H (by rwa [OnePoint.coe_injective hz0] at hz)
  have hA_sub : A₁ ∪ A₂ ⊆ Hs := by
    have hstep : ∀ {A : Set (OnePoint ℂ)} (hA : A ⊆ Hs) {B : Set (OnePoint ℂ)}
        (hB : B ⊆ Hs), A ∪ B ⊆ Hs := by
      intro A hA B hB x hx
      exact hx.elim (fun h => hA h) (fun h => hB h)
    have hA₁sub : A₁ ⊆ Hs := by
      intro x hx
      obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp
        (fun h => hinf (by rw [← h]; exact Or.inl hx))
      rw [hHs]
      refine ⟨z, ?_, hz⟩
      have hzA₁ : ((z : ℂ) : OnePoint ℂ) ∈ A₁ := by rw [hz]; exact hx
      rw [hH]
      by_cases hzF : z ∈ F
      · exact Or.inl (by rw [hW₁]; exact Or.inr hzF)
      · exact Or.inl (by rw [hW₁]; exact Or.inl (hE₁V₁ (by rw [hE₁]; exact ⟨hzA₁, hzF⟩)))
    have hA₂sub : A₂ ⊆ Hs := by
      intro x hx
      obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp
        (fun h => hinf (by rw [← h]; exact Or.inr hx))
      rw [hHs]
      refine ⟨z, ?_, hz⟩
      have hzA₂ : ((z : ℂ) : OnePoint ℂ) ∈ A₂ := by rw [hz]; exact hx
      rw [hH]
      by_cases hzF : z ∈ F
      · exact Or.inr (by rw [hW₂]; exact Or.inr hzF)
      · exact Or.inr (by rw [hW₂]; exact Or.inl (hE₂V₂ (by rw [hE₂]; exact ⟨hzA₂, hzF⟩)))
    exact hstep hA₁sub hA₂sub
  have hHinf : (OnePoint.infty : OnePoint ℂ) ∉
      connectedComponentIn Hsᶜ ((0 : ℂ) : OnePoint ℂ) := by
    have hsub : Hsᶜ ⊆ (A₁ ∪ A₂)ᶜ := fun x hx hxA => hx (hA_sub hxA)
    exact fun hmem => hbad (connectedComponentIn_mono _ hsub hmem)
  -- the winding loop in `H` and the resulting contradiction
  obtain ⟨c, hcH, hcne, hcloop, hidx⟩ := loopIn_open_of_crux hcrux hHso hH0 hHinf
  have hcH' : ∀ t, c t ∈ H := by
    intro t
    have ht := hcH t
    rw [hHs] at ht
    obtain ⟨z, hzH, hzc⟩ := ht
    rwa [OnePoint.coe_injective hzc] at hzH
  exact falseOfLoopWithLog hφcont hφspec hcH' hcloop hidx

end

end Work.JordanSeparation
