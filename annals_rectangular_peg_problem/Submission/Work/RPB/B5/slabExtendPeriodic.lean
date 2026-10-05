import Mathlib
import Submission.Work.RPB.B3.EsTauAux
import Submission.Work.RPB.B3.esTauMultiLin
import Submission.Work.RPB.B5.existsSeeleyWeights

/-!
# Slab extension in the `τ`-variable, preserving `2π`-periodicity in `t`

We extend a `C^n` function `f(τ,t,ρ)` given on the closed slab `[0,1] × ℝ × (-ρ₀,ρ₀)` to the
larger slab `(-ε, 1+ε) × ℝ × (-ρ₀,ρ₀)`, keeping the `2π`-periodicity in `t`.

The construction is the finite *Seeley reflection*: near `τ = 0` the extension is
`Σ_j a_j f(c_j τ, t, ρ)` with distinct `c_j ∈ (-1,0)` and weights `a_j` reproducing the moments
`1 = Σ_j a_j c_j^m` for `m ≤ n` (`Work.RPB.B5.existsSeeleyWeights`); the reflection is glued to
`f` across the seam `τ = 0` by the halfspace gluing lemma `hasFTaylorSeriesUpToOn_of_halfspaces`
of `Work.RPB.B3.EsTauAux`, the jet matching being `gTauJetMatchR` below (a relaxation of
`Work.RPB.B3.esTauJetMatchR` to arbitrary boxes `(-L, M)`).

The same construction is applied at `τ = 1` after the substitution `σ = 1 - τ`.
-/

open scoped ContDiff Topology
open Filter Set

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- The open box `(-L, M) × ℝ × (-ρ, ρ)`. -/
def gBox (L M ρ : ℝ) : Set (ℝ × (ℝ × ℝ)) := Set.Ioo (-L) M ×ˢ Set.univ ×ˢ Set.Ioo (-ρ) ρ

/-- The left half `{τ ≤ 0}` of the box. -/
def gBoxL (L M ρ : ℝ) : Set (ℝ × (ℝ × ℝ)) := gBox L M ρ ∩ {z | z.1 ≤ 0}

/-- The right half `{0 ≤ τ}` of the box. -/
def gBoxR (L M ρ : ℝ) : Set (ℝ × (ℝ × ℝ)) := gBox L M ρ ∩ {z | 0 ≤ z.1}

/-- The half-band `(B, 0] × ℝ × (-ρ, ρ)`. -/
def gBand (B ρ : ℝ) : Set (ℝ × (ℝ × ℝ)) := Set.Ioc B 0 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ) ρ

theorem mem_gBox {L M ρ : ℝ} {z : ℝ × (ℝ × ℝ)} :
    z ∈ gBox L M ρ ↔ z.1 ∈ Set.Ioo (-L) M ∧ z.2.2 ∈ Set.Ioo (-ρ) ρ := by
  simp [gBox, and_assoc]

theorem mem_gBand {B ρ : ℝ} {z : ℝ × (ℝ × ℝ)} :
    z ∈ gBand B ρ ↔ z.1 ∈ Set.Ioc B 0 ∧ z.2.2 ∈ Set.Ioo (-ρ) ρ := by
  simp [gBand, and_assoc]

theorem mem_gBoxR {L M ρ : ℝ} {z : ℝ × (ℝ × ℝ)} :
    z ∈ gBoxR L M ρ ↔ (z.1 ∈ Set.Ioo (-L) M ∧ z.2.2 ∈ Set.Ioo (-ρ) ρ) ∧ 0 ≤ z.1 := by
  rw [gBoxR, Set.mem_inter_iff, mem_gBox, Set.mem_setOf_eq]

theorem isOpen_gBox (L M ρ : ℝ) : IsOpen (gBox L M ρ) :=
  isOpen_Ioo.prod (isOpen_univ.prod isOpen_Ioo)

theorem convex_gBox (L M ρ : ℝ) : Convex ℝ (gBox L M ρ) :=
  (convex_Ioo (-L) M).prod (convex_univ.prod (convex_Ioo (-ρ) ρ))

theorem convex_gBoxL (L M ρ : ℝ) : Convex ℝ (gBoxL L M ρ) := by
  have h : gBoxL L M ρ = gBox L M ρ ∩ ((Set.Iic (0 : ℝ)) ×ˢ Set.univ) := by
    ext z
    simp only [gBoxL, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iic,
      Set.mem_univ, and_true]
  rw [h]
  exact (convex_gBox L M ρ).inter ((convex_Iic (0 : ℝ)).prod convex_univ)

theorem convex_gBoxR (L M ρ : ℝ) : Convex ℝ (gBoxR L M ρ) := by
  have h : gBoxR L M ρ = gBox L M ρ ∩ ((Set.Ici (0 : ℝ)) ×ˢ Set.univ) := by
    ext z
    simp only [gBoxR, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ici,
      Set.mem_univ, and_true]
  rw [h]
  exact (convex_gBox L M ρ).inter ((convex_Ici (0 : ℝ)).prod convex_univ)

theorem convex_gBand {B ρ : ℝ} (hB : B < 0) : Convex ℝ (gBand B ρ) :=
  (convex_Ioc B 0).prod (convex_univ.prod (convex_Ioo (-ρ) ρ))

theorem uniqueDiffOn_gBox (L M ρ : ℝ) : UniqueDiffOn ℝ (gBox L M ρ) :=
  (isOpen_gBox L M ρ).uniqueDiffOn

theorem uniqueDiffOn_gBoxL {L M ρ : ℝ} (hL : 0 < L) (hM : 0 < M) (hρ : 0 < ρ) :
    UniqueDiffOn ℝ (gBoxL L M ρ) := by
  refine uniqueDiffOn_convex (convex_gBoxL L M ρ) ⟨(-L / 2, 0, 0), ?_⟩
  rw [mem_interior_iff_mem_nhds]
  have hsub : (Set.Ioo (-L) 0 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ) ρ) ⊆ gBoxL L M ρ := by
    intro z hz
    refine ⟨?_, ?_⟩
    · rw [mem_gBox]
      exact ⟨⟨hz.1.1, by linarith [hz.1.2, hM]⟩, hz.2.2⟩
    · exact le_of_lt hz.1.2
  exact mem_of_superset
    ((isOpen_Ioo.prod (isOpen_univ.prod isOpen_Ioo)).mem_nhds
      (by refine ⟨⟨by linarith, by linarith⟩, trivial, ⟨by linarith, by linarith⟩⟩)) hsub

theorem uniqueDiffOn_gBoxR {L M ρ : ℝ} (hL : 0 < L) (hM : 0 < M) (hρ : 0 < ρ) :
    UniqueDiffOn ℝ (gBoxR L M ρ) := by
  refine uniqueDiffOn_convex (convex_gBoxR L M ρ) ⟨(M / 2, 0, 0), ?_⟩
  rw [mem_interior_iff_mem_nhds]
  have hsub : (Set.Ioo 0 M ×ˢ Set.univ ×ˢ Set.Ioo (-ρ) ρ) ⊆ gBoxR L M ρ := by
    intro z hz
    refine ⟨?_, ?_⟩
    · rw [mem_gBox]
      exact ⟨⟨by linarith [hz.1.1, hL], hz.1.2⟩, hz.2.2⟩
    · exact le_of_lt hz.1.1
  exact mem_of_superset
    ((isOpen_Ioo.prod (isOpen_univ.prod isOpen_Ioo)).mem_nhds
      (by refine ⟨⟨by linarith, by linarith⟩, trivial, ⟨by linarith, by linarith⟩⟩)) hsub

theorem uniqueDiffOn_gBand {B ρ : ℝ} (hB : B < 0) (hρ : 0 < ρ) :
    UniqueDiffOn ℝ (gBand B ρ) := by
  refine uniqueDiffOn_convex (convex_gBand hB) ⟨(B / 2, 0, 0), ?_⟩
  rw [mem_interior_iff_mem_nhds]
  have hsub : (Set.Ioo B 0 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ) ρ) ⊆ gBand B ρ := by
    intro z hz
    rw [mem_gBand]
    exact ⟨⟨hz.1.1, le_of_lt hz.1.2⟩, hz.2.2⟩
  exact mem_of_superset
    ((isOpen_Ioo.prod (isOpen_univ.prod isOpen_Ioo)).mem_nhds
      (by refine ⟨⟨by linarith, by linarith⟩, trivial, ⟨by linarith, by linarith⟩⟩)) hsub

/-- The preimage of the right half under the reflection `reflLin c` (`c < 0`) is a half-band. -/
theorem preimage_gBoxR {L M ρ c : ℝ} (hL : 0 < L) (hM : 0 < M) (hc : c < 0) :
    Work.RPB.B3.reflLin c ⁻¹' gBoxR L M ρ = gBand (M / c) ρ := by
  ext z
  obtain ⟨τ, t, r⟩ := z
  have hmain : ((c * τ ∈ Set.Ioo (-L) M ∧ r ∈ Set.Ioo (-ρ) ρ) ∧ 0 ≤ c * τ)
      ↔ ((M / c < τ ∧ τ ≤ 0) ∧ r ∈ Set.Ioo (-ρ) ρ) := by
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨(div_lt_iff_of_neg hc).mpr ?_, by nlinarith [h3, hc]⟩, h2⟩
      rw [mul_comm]; exact h1.2
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨⟨by nlinarith [h2, hc, hL],
          by have := (div_lt_iff_of_neg hc).mp h1; nlinarith⟩, h3⟩,
        by nlinarith [h2, hc]⟩
  show (Work.RPB.B3.reflLin c (τ, t, r) ∈ gBoxR L M ρ) ↔ ((τ, t, r) ∈ gBand (M / c) ρ)
  rw [Work.RPB.B3.reflLin_apply, gBoxR, Set.mem_inter_iff, mem_gBox, Set.mem_setOf_eq,
    mem_gBand]
  simp only [Set.mem_Ioc]
  exact hmain

theorem gBoxL_eq_gBand (L M ρ : ℝ) (hM : 0 < M) : gBoxL L M ρ = gBand (-L) ρ := by
  ext z
  rw [gBoxL, Set.mem_inter_iff, mem_gBox, mem_gBand]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1.1, h3⟩, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨⟨h1, by linarith⟩, h3⟩, h2⟩

theorem gBoxL_subset_preimage {L M ρ c : ℝ} (hL : 0 < L) (hc : c < 0) (hcL : M / c ≤ -L) :
    gBoxL L M ρ ⊆ Work.RPB.B3.reflLin c ⁻¹' gBoxR L M ρ := by
  intro z hz
  obtain ⟨τ, t, r⟩ := z
  rw [gBoxL, Set.mem_inter_iff, mem_gBox, Set.mem_setOf_eq] at hz
  obtain ⟨⟨hLt, hMt⟩, hρ⟩ := hz.1
  have hzle : τ ≤ 0 := hz.2
  rw [Set.mem_preimage, Work.RPB.B3.reflLin_apply, gBoxR, Set.mem_inter_iff, mem_gBox,
    Set.mem_setOf_eq]
  refine ⟨⟨⟨?_, ?_⟩, hρ⟩, ?_⟩
  · have h0 : 0 ≤ c * τ := by nlinarith [hzle, hc]
    linarith
  · have hlt : M / c < τ := lt_of_le_of_lt hcL hLt
    have h := (div_lt_iff_of_neg hc).mp hlt
    rw [mul_comm]; exact h
  · nlinarith [hzle, hc]

theorem gBand_eventuallyEq {B B' ρ : ℝ} (hB : B < 0) (hB' : B' < 0)
    {z : ℝ × (ℝ × ℝ)} (hz : z.1 = 0) :
    gBand B ρ =ᶠ[𝓝 z] gBand B' ρ := by
  have hmem : ({w : ℝ × (ℝ × ℝ) | max B B' < w.1}) ∈ 𝓝 z :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds
      (by show max B B' < z.1; rw [hz]; exact max_lt hB hB')
  refine Filter.eventually_of_mem hmem fun w hw => ?_
  apply propext
  change (w ∈ gBand B ρ) ↔ (w ∈ gBand B' ρ)
  rw [mem_gBand, mem_gBand]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨lt_of_le_of_lt (le_max_right B B') hw, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨lt_of_le_of_lt (le_max_left B B') hw, h2⟩, h3⟩

/-- **Jet matching, right half, asymmetric box.**  If `h` is `C^N` on the right half of the box
`(-L, M) × ℝ × (-ρ,ρ)`, then the finite reflection `z ↦ ∑ j, a j • h (reflLin (c j) ·)`, whose
weights reproduce `1` on the powers of `c j` up to order `N`, has the same iterated derivatives as
`h` at the seam `τ = 0`.  (Relaxation of `Work.RPB.B3.esTauJetMatchR` to `(-L, M)`.) -/
theorem gTauJetMatchR {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ × (ℝ × ℝ) → E) (N : ℕ) {L M ρ : ℝ} (hL : 0 < L) (hM : 0 < M) (hρ : 0 < ρ)
    (hh : ContDiffOn ℝ N h (gBoxR L M ρ))
    {n : ℕ} (c a : Fin n → ℝ) (hc : ∀ j, c j < 0) (hcL : ∀ j, M / c j ≤ -L)
    (hid : ∀ m : ℕ, m ≤ N → ∑ j, a j * (c j)^m = 1) :
    ∀ z ∈ gBox L M ρ, z.1 = 0 → ∀ m : ℕ, m ≤ N →
      iteratedFDerivWithin ℝ m (fun z => ∑ j, a j • h (Work.RPB.B3.reflLin (c j) z))
          (gBoxL L M ρ) z
        = iteratedFDerivWithin ℝ m h (gBoxR L M ρ) z := by
  intro z hzbox hz0 m hm
  have hzL : z ∈ gBoxL L M ρ := ⟨hzbox, by show z.1 ≤ 0; rw [hz0]⟩
  have hneg : ∀ j, M / c j < 0 := fun j => div_neg_of_pos_of_neg hM (hc j)
  have hcd : ∀ j, ContDiffWithinAt ℝ m (fun z => h (Work.RPB.B3.reflLin (c j) z))
      (gBoxL L M ρ) z := fun j =>
    (((hh.comp_continuousLinearMap (Work.RPB.B3.reflLin (c j))).mono
      (gBoxL_subset_preimage hL (hc j) (hcL j))).of_le (Nat.cast_le.mpr hm)).contDiffWithinAt hzL
  have hsummand : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      ContDiffWithinAt ℝ m (fun z => a j • h (Work.RPB.B3.reflLin (c j) z)) (gBoxL L M ρ) z :=
    fun j _ => (hcd j).const_smul (a j)
  have hstep1 : iteratedFDerivWithin ℝ m (fun z => ∑ j, a j • h (Work.RPB.B3.reflLin (c j) z))
        (gBoxL L M ρ) z
      = ∑ j, a j • iteratedFDerivWithin ℝ m (fun z => h (Work.RPB.B3.reflLin (c j) z))
          (gBoxL L M ρ) z := by
    rw [iteratedFDerivWithin_fun_sum_apply (uniqueDiffOn_gBoxL hL hM hρ) hzL hsummand]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact iteratedFDerivWithin_const_smul_apply (hcd j) (uniqueDiffOn_gBoxL hL hM hρ) hzL
  have hstep2 : ∀ j, iteratedFDerivWithin ℝ m (fun z => h (Work.RPB.B3.reflLin (c j) z))
        (gBoxL L M ρ) z
      = (iteratedFDerivWithin ℝ m h (gBoxR L M ρ) (Work.RPB.B3.reflLin (c j) z)).compContinuousLinearMap
          (fun _ : Fin m => Work.RPB.B3.reflLin (c j)) := by
    intro j
    have hUdiff : UniqueDiffOn ℝ ((Work.RPB.B3.reflLin (c j)) ⁻¹' gBoxR L M ρ) := by
      rw [preimage_gBoxR hL hM (hc j)]
      exact uniqueDiffOn_gBand (hneg j) hρ
    have hev : gBoxL L M ρ =ᶠ[𝓝 z] ((Work.RPB.B3.reflLin (c j)) ⁻¹' gBoxR L M ρ) := by
      rw [gBoxL_eq_gBand L M ρ hM, preimage_gBoxR hL hM (hc j)]
      exact gBand_eventuallyEq (B' := M / c j) (by linarith [hL]) (hneg j) hz0
    rw [iteratedFDerivWithin_congr_set hev m]
    exact ContinuousLinearMap.iteratedFDerivWithin_comp_right (Work.RPB.B3.reflLin (c j))
      (hh.of_le (Nat.cast_le.mpr hm))
      (uniqueDiffOn_gBoxR hL hM hρ) hUdiff (gBoxL_subset_preimage hL (hc j) (hcL j) hzL) le_rfl
  have hstep3 : (∑ j, a j • iteratedFDerivWithin ℝ m (fun z => h (Work.RPB.B3.reflLin (c j) z))
        (gBoxL L M ρ) z) = iteratedFDerivWithin ℝ m h (gBoxR L M ρ) z := by
    have hzj : ∀ j, Work.RPB.B3.reflLin (c j) z = z := fun j => by
      obtain ⟨τ, s, r⟩ := z
      simp only at hz0
      simp [Work.RPB.B3.reflLin_apply, hz0]
    simp only [hstep2, hzj]
    exact Work.RPB.B3.esTauMultiLin c a (fun m' hm' => hid m' (le_trans hm' hm))
      (iteratedFDerivWithin ℝ m h (gBoxR L M ρ) z)
  rw [hstep1, hstep3]

/-- **One-seam extension.**  A `C^n` function on the right half `{0 ≤ τ}` of the box
`(-L,M) × ℝ × (-ρ,ρ)` extends to a `C^n` function on the whole box, by the finite reflection
`Σ_j a_j h(c_j τ, t, ρ)` glued across the seam `τ = 0`; the extension is periodic in `t` when `h`
is. -/
theorem seamExtend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ × (ℝ × ℝ) → E) (n : ℕ) {L M ρ : ℝ}
    (hL : 0 < L) (hM : 0 < M) (hρ : 0 < ρ)
    (hh : ContDiffOn ℝ n h (gBoxR L M ρ))
    (hper : ∀ τ t ρ, h (τ, t + 2 * Real.pi, ρ) = h (τ, t, ρ)) :
    ∃ F : ℝ × (ℝ × ℝ) → E,
      ContDiffOn ℝ n F (gBox L M ρ) ∧
      (∀ z ∈ gBoxR L M ρ, F z = h z) ∧
      (∀ τ t ρ, F (τ, t + 2 * Real.pi, ρ) = F (τ, t, ρ)) := by
  classical
  have hnpos : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have hML : (0:ℝ) < M / L := div_pos hM hL
  let nod : Fin (n+1) → ℝ := fun j => -((M / L) / (2 * ((n:ℝ) + 1))) * ((j:ℝ) + 1)
  have hnodval : ∀ j, nod j = -((M / L) / (2 * ((n:ℝ) + 1))) * ((j:ℝ) + 1) := fun j => rfl
  have hc0 : (0:ℝ) < (M / L) / (2 * ((n:ℝ) + 1)) := by positivity
  have hs_lt : ∀ j, nod j < 0 := by
    intro j
    rw [hnodval j]
    have hj : (0:ℝ) < (j:ℝ) + 1 := by positivity
    nlinarith [hc0, hj]
  have hs_inj : Function.Injective nod := by
    intro i j hij
    rw [hnodval i, hnodval j] at hij
    have hsum : ((i:ℝ) + 1) = ((j:ℝ) + 1) :=
      mul_left_cancel₀ (ne_of_gt hc0) (by linarith [hij])
    exact Fin.ext (by exact_mod_cast (by linarith [hsum] : (i:ℝ) = (j:ℝ)))
  have hbound : ∀ j, M / nod j = -L * (2 * ((n:ℝ)+1) / ((j:ℝ)+1)) := by
    intro j
    have hj : ((j:ℝ) + 1) ≠ 0 := by positivity
    have hMne : M ≠ 0 := ne_of_gt hM
    have hLne : L ≠ 0 := ne_of_gt hL
    have hnne : ((n:ℝ) + 1) ≠ 0 := ne_of_gt hnpos
    rw [hnodval j]
    field_simp
  have hcL : ∀ j, M / nod j ≤ -L := by
    intro j
    rw [hbound j]
    have hj1 : (0:ℝ) < (j:ℝ) + 1 := by positivity
    have hle : (1:ℝ) ≤ 2 * ((n:ℝ)+1) / ((j:ℝ)+1) := by
      rw [le_div_iff₀ hj1]
      have hjn : (j:ℝ) + 1 ≤ (n:ℝ) + 1 := by
        have h : (j:ℕ) + 1 ≤ n + 1 := Nat.succ_le_iff.mpr j.isLt
        exact_mod_cast h
      nlinarith [hjn, hnpos]
    nlinarith [hle, hL]
  obtain ⟨a, ha⟩ := Work.RPB.B5.existsSeeleyWeights n nod hs_inj
  have hid : ∀ m : ℕ, m ≤ n → ∑ j, a j * (nod j)^m = 1 := fun m hm =>
    ha ⟨m, Nat.lt_succ_of_le hm⟩
  have hsum1 : ∑ j, a j = 1 := by
    have := ha 0
    simpa using this
  let G : ℝ × (ℝ × ℝ) → E := fun z => ∑ j, a j • h (Work.RPB.B3.reflLin (nod j) z)
  have hG : ContDiffOn ℝ n G (gBoxL L M ρ) := by
    refine ContDiffOn.sum (f := fun j z => a j • h (Work.RPB.B3.reflLin (nod j) z)) ?_
    intro j _
    exact (((hh.comp_continuousLinearMap (Work.RPB.B3.reflLin (nod j))).mono
      (gBoxL_subset_preimage hL (hs_lt j) (hcL j))).const_smul (a j))
  let F : ℝ × (ℝ × ℝ) → E := fun z => if z.1 ≤ 0 then G z else h z
  have hFeqR : ∀ z ∈ gBoxR L M ρ, F z = h z := by
    intro z hz
    show (if z.1 ≤ 0 then G z else h z) = h z
    by_cases hlt : z.1 ≤ 0
    · rw [if_pos hlt]
      have hz0 : z.1 = 0 := le_antisymm hlt hz.2
      show (∑ j, a j • h (Work.RPB.B3.reflLin (nod j) z)) = h z
      have hzj : ∀ j, Work.RPB.B3.reflLin (nod j) z = z := fun j => by
        obtain ⟨τ, s', r⟩ := z
        simp only at hz0
        simp [Work.RPB.B3.reflLin_apply, hz0]
      simp only [hzj, ← Finset.sum_smul, hsum1, one_smul]
    · rw [if_neg hlt]
  have hFeqL : ∀ z ∈ gBoxL L M ρ, F z = G z := fun z hz => by
    have hzle : z.1 ≤ 0 := hz.2
    show (if z.1 ≤ 0 then G z else h z) = G z
    rw [if_pos hzle]
  have hjetG := hG.ftaylorSeriesWithin (uniqueDiffOn_gBoxL hL hM hρ)
  have hjetH := hh.ftaylorSeriesWithin (uniqueDiffOn_gBoxR hL hM hρ)
  let p : ℝ × (ℝ × ℝ) → FormalMultilinearSeries ℝ (ℝ × (ℝ × ℝ)) E :=
    fun z => if z.1 ≤ 0 then ftaylorSeriesWithin ℝ G (gBoxL L M ρ) z
             else ftaylorSeriesWithin ℝ h (gBoxR L M ρ) z
  have hpval : ∀ z, p z = (if z.1 ≤ 0 then ftaylorSeriesWithin ℝ G (gBoxL L M ρ) z
             else ftaylorSeriesWithin ℝ h (gBoxR L M ρ) z) := fun z => rfl
  have hFL : HasFTaylorSeriesUpToOn (n : WithTop ENat) F p (gBoxL L M ρ) := by
    refine (hjetG.congr hFeqL).congr_series (fun m hm => fun z hz => ?_)
    have hzle : z.1 ≤ 0 := hz.2
    show ftaylorSeriesWithin ℝ G (gBoxL L M ρ) z m = p z m
    rw [hpval z, if_pos hzle]
  have hFR : HasFTaylorSeriesUpToOn (n : WithTop ENat) F p (gBoxR L M ρ) := by
    refine (hjetH.congr hFeqR).congr_series (fun m hm => fun z hz => ?_)
    show ftaylorSeriesWithin ℝ h (gBoxR L M ρ) z m = p z m
    rw [hpval z]
    by_cases hlt : z.1 ≤ 0
    · rw [if_pos hlt]
      have hz0 : z.1 = 0 := le_antisymm hlt hz.2
      have hzbox : z ∈ gBox L M ρ := hz.1
      show iteratedFDerivWithin ℝ m h (gBoxR L M ρ) z
        = iteratedFDerivWithin ℝ m G (gBoxL L M ρ) z
      exact (gTauJetMatchR h n hL hM hρ hh nod a hs_lt hcL hid z hzbox hz0 m (by exact_mod_cast hm)).symm
    · rw [if_neg hlt]
  refine ⟨F, (Work.RPB.B3.hasFTaylorSeriesUpToOn_of_halfspaces F n (isOpen_gBox L M ρ)
    hFL hFR).contDiffOn, hFeqR, ?_⟩
  intro τ t ρ'
  by_cases hlt : τ ≤ 0
  · show (if τ ≤ 0 then G (τ, t + 2*Real.pi, ρ') else h (τ, t + 2*Real.pi, ρ'))
      = (if τ ≤ 0 then G (τ, t, ρ') else h (τ, t, ρ'))
    rw [if_pos hlt, if_pos hlt]
    show (∑ j, a j • h (Work.RPB.B3.reflLin (nod j) (τ, t + 2*Real.pi, ρ')))
      = (∑ j, a j • h (Work.RPB.B3.reflLin (nod j) (τ, t, ρ')))
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Work.RPB.B3.reflLin_apply, Work.RPB.B3.reflLin_apply, hper (nod j * τ) t ρ']
  · show (if τ ≤ 0 then G (τ, t + 2*Real.pi, ρ') else h (τ, t + 2*Real.pi, ρ'))
      = (if τ ≤ 0 then G (τ, t, ρ') else h (τ, t, ρ'))
    rw [if_neg hlt, if_neg hlt]
    exact hper τ t ρ'

theorem slabExtendPeriodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → ℝ → ℝ → E) (n : ℕ) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (ε : ℝ) (hε : 0 < ε)
    (hf : ContDiffOn ℝ n (fun z : ℝ × (ℝ × ℝ) => f z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hper : ∀ τ t ρ, f τ (t + 2 * Real.pi) ρ = f τ t ρ) :
    ∃ F : ℝ → ℝ → ℝ → E,
      ContDiffOn ℝ n (fun z : ℝ × (ℝ × ℝ) => F z.1 z.2.1 z.2.2)
        (Set.Ioo (-ε) (1 + ε) ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ ρ ∈ Set.Ioo (-ρ₀) ρ₀, F τ t ρ = f τ t ρ) ∧
      (∀ τ t ρ, F τ (t + 2 * Real.pi) ρ = F τ t ρ) := by
  classical
  have hL : (0:ℝ) < ε := hε
  have hM : (0:ℝ) < 3/4 := by norm_num
  -- the function on the box and its right-half smoothness
  let hF : ℝ × (ℝ × ℝ) → E := fun z => f z.1 z.2.1 z.2.2
  have hh0 : ContDiffOn ℝ n hF (gBoxR ε (3/4) ρ₀) := by
    refine hf.mono ?_
    rintro z ⟨⟨hzτ, -, hzρ⟩, hzge⟩
    exact ⟨⟨hzge, le_of_lt (lt_of_lt_of_le hzτ.2 (by norm_num))⟩, trivial, hzρ⟩
  have hper0 : ∀ τ t ρ, hF (τ, t + 2 * Real.pi, ρ) = hF (τ, t, ρ) := fun τ t ρ => hper τ t ρ
  obtain ⟨F0, hF0cd, hF0Req, hF0per⟩ := seamExtend hF n hL hM hρ₀ hh0 hper0
  -- the substitution `σ = 1 - τ` for the seam at `τ = 1`
  let hF1 : ℝ × (ℝ × ℝ) → E := fun z => f (1 - z.1) z.2.1 z.2.2
  have hh1 : ContDiffOn ℝ n hF1 (gBoxR ε (3/4) ρ₀) := by
    have hφ : ContDiffOn ℝ n (fun z : ℝ × (ℝ × ℝ) => ((1 - z.1, (z.2.1, z.2.2)) : ℝ × (ℝ × ℝ)))
        (gBoxR ε (3/4) ρ₀) := by fun_prop
    have hmem : ∀ z ∈ gBoxR ε (3/4) ρ₀,
        (1 - z.1, (z.2.1, z.2.2)) ∈ (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) := by
      rintro z ⟨⟨hzτ, -, hzρ⟩, hzge⟩
      have hzg : 0 ≤ z.1 := hzge
      exact ⟨⟨by linarith [hzτ.2], by linarith [hzg]⟩, trivial, hzρ⟩
    have h := hf.comp hφ hmem
    simpa only [hF1, hF, Function.comp_def] using h
  have hper1 : ∀ τ t ρ, hF1 (τ, t + 2 * Real.pi, ρ) = hF1 (τ, t, ρ) := fun τ t ρ => hper _ t ρ
  obtain ⟨F1, hF1cd, hF1Req, hF1per⟩ := seamExtend hF1 n hL hM hρ₀ hh1 hper1
  -- the assembled function
  let Fr : ℝ × (ℝ × ℝ) → E := fun z =>
    if z.1 < 0 then F0 z
    else if z.1 ≤ 1 then hF z
    else F1 (1 - z.1, z.2.1, z.2.2)
  -- C^n on the seam-0 box
  have hFreq1 : ∀ z ∈ gBox ε (3/4) ρ₀, Fr z = F0 z := by
    intro z hz
    rw [mem_gBox] at hz
    show (if z.1 < 0 then F0 z else if z.1 ≤ 1 then hF z
        else F1 (1 - z.1, z.2.1, z.2.2)) = F0 z
    by_cases h : z.1 < 0
    · rw [if_pos h]
    · rw [if_neg h]
      rw [if_pos (by linarith [hz.1.2] : z.1 ≤ 1)]
      exact (hF0Req z (mem_gBoxR.mpr ⟨hz, by linarith [not_lt.mp h]⟩)).symm
  have hFrc1 : ContDiffOn ℝ n Fr (gBox ε (3/4) ρ₀) := hF0cd.congr hFreq1
  -- C^n on the seam-1 box
  let F1r : ℝ × (ℝ × ℝ) → E := fun z => F1 (1 - z.1, z.2.1, z.2.2)
  have hF1r : ContDiffOn ℝ n F1r (Set.Ioo (1/4:ℝ) (1+ε) ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) := by
    have hφ : ContDiffOn ℝ n (fun z : ℝ × (ℝ × ℝ) => ((1 - z.1, (z.2.1, z.2.2)) : ℝ × (ℝ × ℝ)))
        (Set.Ioo (1/4:ℝ) (1+ε) ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) := by fun_prop
    have hmem : ∀ z ∈ Set.Ioo (1/4:ℝ) (1+ε) ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀,
        (1 - z.1, (z.2.1, z.2.2)) ∈ gBox ε (3/4) ρ₀ := by
      rintro z ⟨hzτ, -, hzρ⟩
      exact mem_gBox.mpr ⟨⟨by linarith [hzτ.2], by linarith [hzτ.1]⟩, hzρ⟩
    have h := hF1cd.comp hφ hmem
    simpa only [F1r, Function.comp_def] using h
  have hFrEq2 : ∀ z ∈ Set.Ioo (1/4:ℝ) (1+ε) ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀, Fr z = F1r z := by
    rintro z ⟨hzτ, -, hzρ⟩
    have hz1 : (1/4:ℝ) < z.1 := hzτ.1
    have hz2 : z.1 < 1 + ε := hzτ.2
    show (if z.1 < 0 then F0 z else if z.1 ≤ 1 then hF z
        else F1 (1 - z.1, z.2.1, z.2.2)) = F1 (1 - z.1, z.2.1, z.2.2)
    rw [if_neg (by linarith)]
    by_cases h : z.1 ≤ 1
    · rw [if_pos h]
      have hσ : ((1 - z.1, z.2.1, z.2.2) : ℝ × (ℝ × ℝ)) ∈ gBoxR ε (3/4) ρ₀ := by
        refine ⟨?_, ?_⟩
        · exact mem_gBox.mpr ⟨⟨by linarith, by linarith⟩, hzρ⟩
        · show 0 ≤ 1 - z.1; linarith
      rw [hF1Req _ hσ]
      show hF z = hF1 (1 - z.1, z.2.1, z.2.2)
      show f z.1 z.2.1 z.2.2 = f (1 - (1 - z.1)) z.2.1 z.2.2
      rw [show (1:ℝ) - (1 - z.1) = z.1 by ring]
    · rw [if_neg h]
  have hFrc2 : ContDiffOn ℝ n Fr (Set.Ioo (1/4:ℝ) (1+ε) ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) :=
    hF1r.congr hFrEq2
  -- global C^n on the target
  have hFrcd : ContDiffOn ℝ n Fr (Set.Ioo (-ε) (1 + ε) ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) := by
    refine contDiffOn_of_locally_contDiffOn (fun z hz => ?_)
    by_cases h : z.1 < 3/4
    · refine ⟨gBox ε (3/4) ρ₀, isOpen_gBox _ _ _, ?_, ?_⟩
      · exact mem_gBox.mpr ⟨⟨hz.1.1, h⟩, hz.2.2⟩
      · exact hFrc1.mono Set.inter_subset_right
    · refine ⟨Set.Ioo (1/4:ℝ) (1+ε) ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀,
        isOpen_Ioo.prod (isOpen_univ.prod isOpen_Ioo), ?_, ?_⟩
      · exact ⟨⟨by linarith, hz.1.2⟩, trivial, hz.2.2⟩
      · exact hFrc2.mono Set.inter_subset_right
  refine ⟨fun τ t ρ => Fr (τ, t, ρ), ?_, ?_, ?_⟩
  · exact hFrcd
  · intro τ hτ t ρ hρ
    show Fr (τ, t, ρ) = f τ t ρ
    have hrw : Fr (τ, t, ρ) = (if τ < 0 then F0 (τ, t, ρ) else if τ ≤ 1 then hF (τ, t, ρ)
        else F1 (1 - τ, t, ρ)) := rfl
    rw [hrw]
    simp only [if_neg (not_lt.mpr hτ.1), if_pos hτ.2]
    rfl
  · intro τ t ρ
    show Fr (τ, t + 2*Real.pi, ρ) = Fr (τ, t, ρ)
    have hrw : ∀ t' : ℝ, Fr (τ, t', ρ) = (if τ < 0 then F0 (τ, t', ρ)
        else if τ ≤ 1 then hF (τ, t', ρ) else F1 (1 - τ, t', ρ)) := fun t' => rfl
    rw [hrw (t + 2*Real.pi), hrw t]
    by_cases h : τ < 0
    · simp only [if_pos h]
      exact hF0per τ t ρ
    · simp only [if_neg h]
      by_cases h1 : τ ≤ 1
      · simp only [if_pos h1]
        exact hper τ t ρ
      · simp only [if_neg h1]
        exact hF1per (1 - τ) t ρ

end Work.RPB.B5
