/-
Copyright: the martinet_totally_real_towers team.

# Vanishing of `H³` of a compact totally disconnected group with `ℚ`-coefficients

**Module** `Submission.Work.ShafarevichKoch.RatVanishing.subsingleton_H3_rat`.

Let `G` be a group with a topology making it a topological group, compact and totally
disconnected, and let `ℚ` be a discrete `G`-module on which `G` acts trivially.  Then the
continuous cohomology group `H³(G, ℚ)` of the chapter `Submission.Work.ShafarevichKoch`
(`Work.ShafarevichKoch.H3`, built on the `4`-cochains, the third differential `d³` and the
`3`-cocycles of `Submission/Work/ShafarevichKoch/Cohomology3.lean`) is trivial (a subsingleton).

The argument follows the same two-step pattern as the companion file
`subsingleton_H1_H2_rat.lean` for `H¹` and `H²`:

* **Factorisation through a finite quotient.**  A locally constant function on the compact
  group `G × G × G` is invariant under right translation by a small open normal subgroup
  `N ⊴ G` in each of the three variables, so every `3`-cocycle descends to a `3`-cocycle on the
  finite group `G ⧸ N`.  The invariance is obtained from
  `Work.TopologyGroup.exists_openSubgroup_right_invariant` (a locally constant function on a
  compact topological group is right invariant under some open subgroup, applied to `f` on the
  compact group `G × G × G`), passing to the three coordinate subgroups of the resulting open
  subgroup of `G × G × G` and then to an open normal subgroup contained in their intersection.

* **Averaging over the finite group.**  On a finite group `Q`, a `3`-cocycle with coefficients
  in the `ℚ`-vector space `ℚ` is a coboundary: the averaged `2`-cochain
  `x (σ, τ) = -|Q|⁻¹ * ∑_ρ c (σ, τ, ρ)` satisfies `(d²x)(σ,τ,ρ) = c(σ,τ,ρ)`, because the
  cocycle identity rewrites the summand as a difference that telescopes under reindexing.

Pulling the resulting `2`-cochain back along `G → G ⧸ N` gives a locally constant `2`-cochain
whose coboundary is the original `3`-cocycle, whence `B³ = Z³` and `H³(G,ℚ)` is a subsingleton.

The auxiliary lemmas proved here are:
* `exists_openNormalSubgroup_three_slot_invariant` — the factorisation step;
* `exists_coboundary_of_finite_threeCocycle_rat` — the averaging step.
-/

import Mathlib
import Submission.Work.ShafarevichKoch.Cohomology3
import Submission.Work.ShafarevichKoch.RatVanishing.subsingleton_H1_H2_rat
import Submission.Work.TopologyGroup.exists_openSubgroup_right_invariant

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.ShafarevichKoch.RatVanishing

open Work.ConCohomology

/-! ### Invariance of a locally constant function on `G × G × G` under an open normal subgroup -/

/-- **A locally constant function on the cube of a compact totally disconnected group is
invariant, in each variable, under right translation by one open normal subgroup.**

`Work.TopologyGroup.exists_openSubgroup_right_invariant` produces an open subgroup `H` of the
compact group `G × G × G` under whose right translations `f` is invariant.  Intersecting `H` with
the three coordinate subgroups `{a | (a,1,1) ∈ H}`, `{a | (1,a,1) ∈ H}`, `{a | (1,1,a) ∈ H}` gives an
open subgroup `M ≤ G` whose elements act trivially in each variable separately, and any open
normal subgroup `N` of `G` contained in `M` (which exists because `G` is compact and totally
disconnected) does the job. -/
theorem exists_openNormalSubgroup_three_slot_invariant {G M : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {f : G × G × G → M} (hf : IsLocallyConstant f) :
    ∃ N : Subgroup G, N.Normal ∧ IsOpen (N : Set G) ∧
      (∀ n ∈ N, ∀ σ τ ρ : G, f (σ * n, τ, ρ) = f (σ, τ, ρ)) ∧
      (∀ n ∈ N, ∀ σ τ ρ : G, f (σ, τ * n, ρ) = f (σ, τ, ρ)) ∧
      (∀ n ∈ N, ∀ σ τ ρ : G, f (σ, τ, ρ * n) = f (σ, τ, ρ)) := by
  classical
  -- An open subgroup of `G × G × G` acting trivially on the right.
  obtain ⟨H, hH⟩ :=
    Work.TopologyGroup.exists_openSubgroup_right_invariant (G := G × G × G) (M := M) f hf
  -- The three coordinate inclusions `G → G × G × G`.
  let φ₁ : G →* G × G × G :=
    { toFun := fun a => (a, 1, 1)
      map_one' := rfl
      map_mul' := fun a b => by ext <;> simp }
  let φ₂ : G →* G × G × G :=
    { toFun := fun a => (1, a, 1)
      map_one' := rfl
      map_mul' := fun a b => by ext <;> simp }
  let φ₃ : G →* G × G × G :=
    { toFun := fun a => (1, 1, a)
      map_one' := rfl
      map_mul' := fun a b => by ext <;> simp }
  have hφ₁ : Continuous φ₁ := by
    show Continuous fun a : G => (a, 1, 1)
    exact continuous_id.prodMk (continuous_const.prodMk continuous_const)
  have hφ₂ : Continuous φ₂ := by
    show Continuous fun a : G => (1, a, 1)
    exact continuous_const.prodMk (continuous_id.prodMk continuous_const)
  have hφ₃ : Continuous φ₃ := by
    show Continuous fun a : G => (1, 1, a)
    exact continuous_const.prodMk (continuous_const.prodMk continuous_id)
  let H₁ : Subgroup G := (H : Subgroup (G × G × G)).comap φ₁
  let H₂ : Subgroup G := (H : Subgroup (G × G × G)).comap φ₂
  let H₃ : Subgroup G := (H : Subgroup (G × G × G)).comap φ₃
  have hH₁open : IsOpen (H₁ : Set G) := by
    change IsOpen (φ₁ ⁻¹' (H : Set (G × G × G)))
    exact H.isOpen.preimage hφ₁
  have hH₂open : IsOpen (H₂ : Set G) := by
    change IsOpen (φ₂ ⁻¹' (H : Set (G × G × G)))
    exact H.isOpen.preimage hφ₂
  have hH₃open : IsOpen (H₃ : Set G) := by
    change IsOpen (φ₃ ⁻¹' (H : Set (G × G × G)))
    exact H.isOpen.preimage hφ₃
  let Mm : Subgroup G := H₁ ⊓ H₂ ⊓ H₃
  have hMmopen : IsOpen (Mm : Set G) := by
    change IsOpen (((H₁ ⊓ H₂ ⊓ H₃ : Subgroup G)) : Set G)
    rw [Subgroup.coe_inf, Subgroup.coe_inf]
    exact (hH₁open.inter hH₂open).inter hH₃open
  obtain ⟨N, hNsub⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hMmopen Mm.one_mem
  haveI hNnorm : N.toSubgroup.Normal := N.isNormal'
  refine ⟨N.toSubgroup, hNnorm, N.toOpenSubgroup.isOpen, ?_, ?_, ?_⟩
  · -- invariance in the first variable
    intro n hn σ τ ρ
    have hnM : n ∈ Mm := hNsub hn
    have hn1 : n ∈ H₁ := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hnM).1).1
    have hmem : (n, 1, 1) ∈ (H : Subgroup (G × G × G)) := Subgroup.mem_comap.mp hn1
    have := hH (σ, τ, ρ) ⟨(n, 1, 1), hmem⟩
    simpa using this
  · -- invariance in the second variable
    intro n hn σ τ ρ
    have hnM : n ∈ Mm := hNsub hn
    have hn2 : n ∈ H₂ := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hnM).1).2
    have hmem : (1, n, 1) ∈ (H : Subgroup (G × G × G)) := Subgroup.mem_comap.mp hn2
    have := hH (σ, τ, ρ) ⟨(1, n, 1), hmem⟩
    simpa using this
  · -- invariance in the third variable
    intro n hn σ τ ρ
    have hnM : n ∈ Mm := hNsub hn
    have hn3 : n ∈ H₃ := (Subgroup.mem_inf.mp hnM).2
    have hmem : (1, 1, n) ∈ (H : Subgroup (G × G × G)) := Subgroup.mem_comap.mp hn3
    have := hH (σ, τ, ρ) ⟨(1, 1, n), hmem⟩
    simpa using this

/-! ### Averaging a `3`-cocycle over a finite group with coefficients in `ℚ` -/

/-- **Averaging a `3`-cocycle over a finite group, with coefficients in `ℚ`.**  Let `c` be an
inhomogeneous `3`-cocycle (trivial action) on a finite group `Q`.  Then the averaged `2`-cochain
`x (σ, τ) = -|Q|⁻¹ * ∑_ρ c (σ, τ, ρ)` has coboundary `c`:
`x (τ,ρ) - x (σ*τ,ρ) + x (σ,τ*ρ) - x (σ,τ) = c (σ,τ,ρ)`.  The cocycle identity rewrites the
summand as `c (σ,τ,ρ*υ) - c (σ,τ,ρ) - c (σ,τ,υ)`, and the first and third terms cancel after
reindexing `υ ↦ ρ⁻¹υ`; the only point is that `|Q|` is invertible in `ℚ`. -/
theorem exists_coboundary_of_finite_threeCocycle_rat {Q : Type*} [Group Q] [Fintype Q]
    (c : Q → Q → Q → ℚ)
    (hc : ∀ σ τ ρ υ : Q, c τ ρ υ - c (σ * τ) ρ υ + c σ (τ * ρ) υ - c σ τ (ρ * υ) + c σ τ ρ = 0) :
    ∃ x : Q → Q → ℚ, ∀ σ τ ρ : Q, x τ ρ - x (σ * τ) ρ + x σ (τ * ρ) - x σ τ = c σ τ ρ := by
  classical
  have hN : ((Fintype.card Q : ℚ)) ≠ 0 := by
    haveI : Nonempty Q := ⟨1⟩
    exact_mod_cast Fintype.card_ne_zero
  refine ⟨fun σ τ => -(((Fintype.card Q : ℚ))⁻¹ * ∑ ρ : Q, c σ τ ρ), fun σ τ ρ => ?_⟩
  have hstep : ∀ υ : Q, c τ ρ υ - c (σ * τ) ρ υ + c σ (τ * ρ) υ - c σ τ υ
      = c σ τ (ρ * υ) - c σ τ ρ - c σ τ υ := by
    intro υ
    have h := hc σ τ ρ υ
    linarith
  have hreindex : (∑ υ : Q, c σ τ (ρ * υ)) = ∑ υ : Q, c σ τ υ :=
    Equiv.sum_comp (Equiv.mulLeft ρ) (fun υ => c σ τ υ)
  have hsum : (∑ υ : Q, (c τ ρ υ - c (σ * τ) ρ υ + c σ (τ * ρ) υ - c σ τ υ))
      = -((Fintype.card Q : ℚ) * c σ τ ρ) := by
    rw [Finset.sum_congr rfl (fun υ _ => hstep υ)]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hreindex]
    ring
  have hfold : (∑ υ : Q, (c τ ρ υ - c (σ * τ) ρ υ + c σ (τ * ρ) υ - c σ τ υ))
      = (∑ υ : Q, c τ ρ υ) - (∑ υ : Q, c (σ * τ) ρ υ) + (∑ υ : Q, c σ (τ * ρ) υ)
        - (∑ υ : Q, c σ τ υ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have key : ((Fintype.card Q : ℚ))⁻¹ * ((∑ υ : Q, c τ ρ υ) - (∑ υ : Q, c (σ * τ) ρ υ)
      + (∑ υ : Q, c σ (τ * ρ) υ) - (∑ υ : Q, c σ τ υ)) = -c σ τ ρ := by
    rw [← hfold, hsum, mul_neg, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  rw [show -(((Fintype.card Q : ℚ))⁻¹ * ∑ υ : Q, c τ ρ υ)
      - -(((Fintype.card Q : ℚ))⁻¹ * ∑ υ : Q, c (σ * τ) ρ υ)
      + -(((Fintype.card Q : ℚ))⁻¹ * ∑ υ : Q, c σ (τ * ρ) υ)
      - -(((Fintype.card Q : ℚ))⁻¹ * ∑ υ : Q, c σ τ υ)
      = ((Fintype.card Q : ℚ))⁻¹ * (-(∑ υ : Q, c τ ρ υ) + (∑ υ : Q, c (σ * τ) ρ υ)
        - (∑ υ : Q, c σ (τ * ρ) υ) + (∑ υ : Q, c σ τ υ)) from by ring]
  rw [show -(∑ υ : Q, c τ ρ υ) + (∑ υ : Q, c (σ * τ) ρ υ) - (∑ υ : Q, c σ (τ * ρ) υ)
      + (∑ υ : Q, c σ τ υ)
      = -((∑ υ : Q, c τ ρ υ) - (∑ υ : Q, c (σ * τ) ρ υ) + (∑ υ : Q, c σ (τ * ρ) υ)
        - (∑ υ : Q, c σ τ υ)) from by ring]
  rw [mul_neg, key, neg_neg]

/-! ### Vanishing of `H³` -/

/-- **`H³(G, ℚ)` is trivial for a compact totally disconnected `G` acting trivially on `ℚ`.**

A locally constant `3`-cocycle is invariant under right translation by an open normal subgroup
`N ⊴ G` in each variable, hence descends to a `3`-cocycle on the finite group `G ⧸ N`, where it
is a coboundary by the averaging lemma `exists_coboundary_of_finite_threeCocycle_rat`.  Pulling
the resulting `2`-cochain back along `G → G ⧸ N` gives a locally constant `2`-cochain whose
coboundary is the original cocycle; hence `B³ = Z³`. -/
theorem subsingleton_H3_rat {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    [DistribMulAction G ℚ] [Work.ConCohomology.IsDiscreteGModule G ℚ]
    (htriv : ∀ (σ : G) (q : ℚ), σ • q = q) :
    Subsingleton (Work.ShafarevichKoch.H3 G ℚ) := by
  rw [QuotientAddGroup.subsingleton_iff]
  apply le_antisymm le_top
  intro z _
  rw [Work.ShafarevichKoch.mem_B3']
  change (z : Work.ConCohomology.Cochain3 G ℚ) ∈ (Work.ConCohomology.d2Hom G ℚ).range
  set c : G × G × G → ℚ := (z.1 : G × G × G → ℚ) with hc_def
  have hflc : IsLocallyConstant c := by rw [hc_def]; exact z.1.isLocallyConstant
  have hcocyc : ∀ σ τ ρ υ : G,
      c (τ,ρ,υ) - c (σ*τ,ρ,υ) + c (σ,τ*ρ,υ) - c (σ,τ,ρ*υ) + c (σ,τ,ρ) = 0 := by
    intro σ τ ρ υ
    have hker : Work.ShafarevichKoch.d3Hom G ℚ z = 0 := AddMonoidHom.mem_ker.mp z.2
    have h := congrFun (congrArg (fun g : Work.ShafarevichKoch.Cochain4 G ℚ =>
      (g : G × G × G × G → ℚ)) hker) (σ,τ,ρ,υ)
    simp only [Work.ShafarevichKoch.d3Hom_apply] at h
    rw [htriv σ] at h
    exact h
  obtain ⟨N, hNnorm, hNopen, hinv1, hinv2, hinv3⟩ :=
    exists_openNormalSubgroup_three_slot_invariant (f := c) hflc
  haveI : N.Normal := hNnorm
  haveI : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNopen
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  let C : (G ⧸ N) → (G ⧸ N) → (G ⧸ N) → ℚ := fun q₁ q₂ q₃ => c (q₁.out, q₂.out, q₃.out)
  have hcongr : ∀ {u₁ u₂ u₃ v₁ v₂ v₃ : G},
      QuotientGroup.mk' N u₁ = QuotientGroup.mk' N v₁ →
      QuotientGroup.mk' N u₂ = QuotientGroup.mk' N v₂ →
      QuotientGroup.mk' N u₃ = QuotientGroup.mk' N v₃ →
      c (u₁,u₂,u₃) = c (v₁,v₂,v₃) := by
    intro u₁ u₂ u₃ v₁ v₂ v₃ h₁ h₂ h₃
    obtain ⟨z₁, hz₁N, hz₁⟩ := (QuotientGroup.mk'_eq_mk' N).mp h₁
    obtain ⟨z₂, hz₂N, hz₂⟩ := (QuotientGroup.mk'_eq_mk' N).mp h₂
    obtain ⟨z₃, hz₃N, hz₃⟩ := (QuotientGroup.mk'_eq_mk' N).mp h₃
    rw [← hz₁, ← hz₂, ← hz₃]
    rw [hinv1 z₁ hz₁N u₁ (u₂ * z₂) (u₃ * z₃), hinv2 z₂ hz₂N u₁ u₂ (u₃ * z₃),
      hinv3 z₃ hz₃N u₁ u₂ u₃]
  have hC : ∀ q q' q'' q''' : G ⧸ N,
      C q' q'' q''' - C (q*q') q'' q''' + C q (q'*q'') q''' - C q q' (q''*q''')
        + C q q' q'' = 0 := by
    intro q q' q'' q'''
    have e1 : QuotientGroup.mk' N ((q*q').out) = QuotientGroup.mk' N (q.out * q'.out) := by
      simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul]
      rw [QuotientGroup.out_eq' (q*q'), QuotientGroup.out_eq' q, QuotientGroup.out_eq' q']
    have e2 : QuotientGroup.mk' N ((q'*q'').out) = QuotientGroup.mk' N (q'.out * q''.out) := by
      simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul]
      rw [QuotientGroup.out_eq' (q'*q''), QuotientGroup.out_eq' q', QuotientGroup.out_eq' q'']
    have e3 : QuotientGroup.mk' N ((q''*q''').out) = QuotientGroup.mk' N (q''.out * q'''.out) := by
      simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul]
      rw [QuotientGroup.out_eq' (q''*q'''), QuotientGroup.out_eq' q'', QuotientGroup.out_eq' q''']
    have t1 : C (q*q') q'' q''' = c (q.out * q'.out, q''.out, q'''.out) := by
      show c ((q*q').out, q''.out, q'''.out) = c (q.out * q'.out, q''.out, q'''.out)
      exact hcongr e1 rfl rfl
    have t2 : C q (q'*q'') q''' = c (q.out, q'.out * q''.out, q'''.out) := by
      show c (q.out, (q'*q'').out, q'''.out) = c (q.out, q'.out * q''.out, q'''.out)
      exact hcongr rfl e2 rfl
    have t3 : C q q' (q''*q''') = c (q.out, q'.out, q''.out * q'''.out) := by
      show c (q.out, q'.out, (q''*q''').out) = c (q.out, q'.out, q''.out * q'''.out)
      exact hcongr rfl rfl e3
    rw [t1, t2, t3]
    show c (q'.out, q''.out, q'''.out) - c (q.out * q'.out, q''.out, q'''.out)
      + c (q.out, q'.out * q''.out, q'''.out) - c (q.out, q'.out, q''.out * q'''.out)
      + c (q.out, q'.out, q''.out) = 0
    exact hcocyc q.out q'.out q''.out q'''.out
  obtain ⟨x, hx⟩ := exists_coboundary_of_finite_threeCocycle_rat C hC
  have hmk : IsLocallyConstant (fun σ : G => QuotientGroup.mk' N σ) :=
    Work.ConCohomology.isLocallyConstant_of_le_open_ker (QuotientGroup.mk' N) N hNopen
      (by rw [QuotientGroup.ker_mk'])
  have h1 : IsLocallyConstant (fun p : G × G => QuotientGroup.mk' N p.1) :=
    hmk.comp_continuous continuous_fst
  have h2 : IsLocallyConstant (fun p : G × G => QuotientGroup.mk' N p.2) :=
    hmk.comp_continuous continuous_snd
  have hloc : IsLocallyConstant
      (fun p : G × G => x (QuotientGroup.mk' N p.1) (QuotientGroup.mk' N p.2)) :=
    h1.comp₂ h2 (fun a b => x a b)
  refine ⟨⟨fun p : G × G => x (QuotientGroup.mk' N p.1) (QuotientGroup.mk' N p.2), hloc⟩, ?_⟩
  ext p
  obtain ⟨σ, τ, ρ⟩ := p
  simp only [Work.ConCohomology.d2Hom_apply, htriv]
  show x (QuotientGroup.mk' N τ) (QuotientGroup.mk' N ρ)
      - x (QuotientGroup.mk' N (σ*τ)) (QuotientGroup.mk' N ρ)
      + x (QuotientGroup.mk' N σ) (QuotientGroup.mk' N (τ*ρ))
      - x (QuotientGroup.mk' N σ) (QuotientGroup.mk' N τ) = c (σ, τ, ρ)
  rw [show QuotientGroup.mk' N (σ*τ) = QuotientGroup.mk' N σ * QuotientGroup.mk' N τ
        from map_mul _ _ _,
      show QuotientGroup.mk' N (τ*ρ) = QuotientGroup.mk' N τ * QuotientGroup.mk' N ρ
        from map_mul _ _ _]
  rw [hx (QuotientGroup.mk' N σ) (QuotientGroup.mk' N τ) (QuotientGroup.mk' N ρ)]
  show c ((QuotientGroup.mk' N σ).out, (QuotientGroup.mk' N τ).out, (QuotientGroup.mk' N ρ).out)
    = c (σ, τ, ρ)
  exact hcongr (by simp [QuotientGroup.mk'_apply])
    (by simp [QuotientGroup.mk'_apply]) (by simp [QuotientGroup.mk'_apply])

end Work.ShafarevichKoch.RatVanishing
