import Mathlib
import Submission.Work.WilE2.Setup
import Submission.Work.WilE2.local_orbit_covers_eps
import Submission.Work.WilE2.global_integral_curve

open scoped Topology

set_option autoImplicit false

namespace Work.WilE2

/-- Two global integral curves of a `C¹`, locally Lipschitz vector field that agree at one point
are equal. -/
lemma integral_curve_unique {m : ℕ} (X : (Fin m → ℝ) → (Fin m → ℝ)) (hX : ContDiff ℝ 1 X)
    {γ δ : ℝ → Fin m → ℝ} (hγ : ∀ t, HasDerivAt γ (X (γ t)) t)
    (hδ : ∀ t, HasDerivAt δ (X (δ t)) t) {t₀ : ℝ} (h : γ t₀ = δ t₀) : γ = δ := by
  have hcontγ : Continuous γ := continuous_iff_continuousAt.mpr (fun t => (hγ t).continuousAt)
  have hcontδ : Continuous δ := continuous_iff_continuousAt.mpr (fun t => (hδ t).continuousAt)
  have hcl : IsClosed {t : ℝ | γ t = δ t} := isClosed_eq hcontγ hcontδ
  have hne : ({t : ℝ | γ t = δ t}).Nonempty := ⟨t₀, h⟩
  have hopen : IsOpen {t : ℝ | γ t = δ t} := by
    rw [isOpen_iff_mem_nhds]
    intro u hu
    obtain ⟨K, W, hW, hKW⟩ := hX.locallyLipschitz (γ u)
    exact ODE_solution_unique_of_eventually (v := fun _ : ℝ => X) (s := fun _ => W) (K := K)
      (f := γ) (g := δ) (t₀ := u)
      (Filter.Eventually.of_forall (fun _ => hKW))
      (by filter_upwards [(hγ u).continuousAt.preimage_mem_nhds hW] with x hx; exact ⟨hγ x, hx⟩)
      (by filter_upwards [(hδ u).continuousAt.preimage_mem_nhds (hu ▸ hW)] with x hx; exact ⟨hδ x, hx⟩)
      hu
  have hsub := IsPreconnected.subset_isClopen (convex_univ.isPreconnected : IsPreconnected (Set.univ : Set ℝ))
    ⟨hcl, hopen⟩ (by simpa using hne)
  funext t
  exact hsub (Set.mem_univ t)

theorem compact_level_curve_flow {m : ℕ} (V : (Fin m → ℝ) → (Fin (m - 1) → ℝ)) (X : (Fin m → ℝ) → (Fin m → ℝ)) (hV : ContDiff ℝ 1 V) (hX : ContDiff ℝ 1 X) (hC : IsCompact {z | V z = 0}) (hgrad : ∀ z, V z = 0 → LinearIndependent ℝ (fun i => fderiv ℝ (fun w => V w i) z)) (hX0 : ∀ z, V z = 0 → X z ≠ 0) (htan : ∀ z, V z = 0 → ∀ i, fderiv ℝ (fun w => V w i) z (X z) = 0) : ∀ z, V z = 0 → ∃ (T : ℝ) (γ : ℝ → Fin m → ℝ), 0 < T ∧ γ 0 = z ∧ (∀ t, HasDerivAt γ (X (γ t)) t) ∧ (∀ t, V (γ t) = 0) ∧ (∀ t, γ (t + T) = γ t) ∧ Set.range γ = connectedComponentIn {z' | V z' = 0} z := by
  intro z hz
  obtain ⟨γ, hγ0, hγder, hγV⟩ := global_integral_curve V X hV hX hC hgrad hX0 htan z hz
  have hcontγ : Continuous γ := continuous_iff_continuousAt.mpr (fun t => (hγder t).continuousAt)
  -- ## Step B: the image of γ is open in the level set
  have hopen : ∀ p ∈ Set.range γ, ∃ U : Set (Fin m → ℝ),
      IsOpen U ∧ p ∈ U ∧ U ∩ {z | V z = 0} ⊆ Set.range γ := by
    rintro p ⟨t₀, rfl⟩
    obtain ⟨U, ε, hUo, hpU, hε, hU⟩ :=
      local_orbit_covers_eps V X hV hX hgrad hX0 htan (γ t₀) (hγV t₀)
    refine ⟨U, hUo, hpU, ?_⟩
    have hsh0 : (fun u => γ (u + t₀)) 0 = γ t₀ := by simp
    have hshd : ∀ u, HasDerivAt (fun u => γ (u + t₀)) (X ((fun u => γ (u + t₀)) u)) u :=
      fun u => (hγder (u + t₀)).comp_add_const u t₀
    intro w hw
    obtain ⟨s, _, rfl⟩ := hU (fun u => γ (u + t₀)) hsh0 hshd hw
    exact ⟨s + t₀, rfl⟩
  -- ## Step C: the image of γ is closed in the level set
  have hcl : ∀ q ∈ closure (Set.range γ), q ∈ {z | V z = 0} → q ∈ Set.range γ := by
    intro q hq hqC
    by_contra hqR
    obtain ⟨U, ε, hUo, hqU, hε, hU⟩ := local_orbit_covers_eps V X hV hX hgrad hX0 htan q hqC
    have hne : (U ∩ Set.range γ).Nonempty :=
      (mem_closure_iff_nhds.mp hq) U (hUo.mem_nhds hqU)
    obtain ⟨p, hpU, hpR⟩ := hne
    obtain ⟨t₀, rfl⟩ := hpR
    obtain ⟨δ, hδ0, hδder, hδV⟩ := global_integral_curve V X hV hX hC hgrad hX0 htan q hqC
    have hcov := hU δ hδ0 hδder
    obtain ⟨s₀, hs₀, hs₀eq⟩ := hcov ⟨hpU, hγV t₀⟩
    have hγ'0 : (fun u => γ (u + t₀)) 0 = (fun u => δ (u + s₀)) 0 := by
      simp only [zero_add]
      exact hs₀eq.symm
    have hγ'd : ∀ u, HasDerivAt (fun u => γ (u + t₀)) (X ((fun u => γ (u + t₀)) u)) u :=
      fun u => (hγder (u + t₀)).comp_add_const u t₀
    have hδ'd : ∀ u, HasDerivAt (fun u => δ (u + s₀)) (X ((fun u => δ (u + s₀)) u)) u :=
      fun u => (hδder (u + s₀)).comp_add_const u s₀
    have huniq := integral_curve_unique X hX hγ'd hδ'd hγ'0
    have hval : γ (-s₀ + t₀) = δ (-s₀ + s₀) := congrFun huniq (-s₀)
    rw [neg_add_cancel, hδ0] at hval
    have h2 : -s₀ + t₀ = t₀ - s₀ := by ring
    rw [h2] at hval
    exact hqR (hval ▸ ⟨t₀ - s₀, rfl⟩)
  -- ## Step D: the image of γ is the connected component of z
  have hsub1 : Set.range γ ⊆ connectedComponentIn {z | V z = 0} z :=
    IsPreconnected.subset_connectedComponentIn
      (by simpa only [Set.image_univ] using
        (convex_univ.isPreconnected).image γ hcontγ.continuousOn) ⟨0, hγ0⟩
      (by rintro p ⟨t, rfl⟩; exact hγV t)
  have hU'open : IsOpen ({x : ↥{z : Fin m → ℝ | V z = 0} | (x : Fin m → ℝ) ∈ Set.range γ}) := by
    have heq : {x : ↥{z : Fin m → ℝ | V z = 0} | (x : Fin m → ℝ) ∈ Set.range γ}
        = ⋃ (p : ↥(Set.range γ)), (Subtype.val) ⁻¹' ((hopen p.1 p.2).choose) := by
      ext x
      constructor
      · intro hx
        exact Set.mem_iUnion.mpr ⟨⟨(x : Fin m → ℝ), hx⟩, (hopen (x : Fin m → ℝ) hx).choose_spec.2.1⟩
      · intro hx
        obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
        exact (hopen p.1 p.2).choose_spec.2.2 ⟨hp, x.2⟩
    rw [heq]
    exact isOpen_iUnion (fun p => (hopen p.1 p.2).choose_spec.1.preimage continuous_subtype_val)
  have hU'closed : IsClosed ({x : ↥{z : Fin m → ℝ | V z = 0} | (x : Fin m → ℝ) ∈ Set.range γ}) := by
    have heq : {x : ↥{z : Fin m → ℝ | V z = 0} | (x : Fin m → ℝ) ∈ Set.range γ}
        = (Subtype.val) ⁻¹' (closure (Set.range γ)) := by
      ext x
      exact ⟨fun hx => subset_closure hx, fun hx => hcl (x : Fin m → ℝ) hx x.2⟩
    rw [heq]
    exact isClosed_closure.preimage continuous_subtype_val
  have hCz_sub : connectedComponentIn {z | V z = 0} z ⊆ Set.range γ := by
    haveI : CompactSpace ↥{z : Fin m → ℝ | V z = 0} := isCompact_iff_compactSpace.mp hC
    have hzmem : (⟨z, hz⟩ : ↥{z : Fin m → ℝ | V z = 0}) ∈
        {x : ↥{z : Fin m → ℝ | V z = 0} | (x : Fin m → ℝ) ∈ Set.range γ} := ⟨0, hγ0⟩
    have hcc := IsClopen.connectedComponent_subset (⟨hU'closed, hU'open⟩ : IsClopen _) hzmem
    rw [connectedComponentIn_eq_image (F := {z : Fin m → ℝ | V z = 0}) (x := z) hz]
    rintro y ⟨x, hx, rfl⟩
    exact hcc hx
  have hrange_eq : Set.range γ = connectedComponentIn {z | V z = 0} z := le_antisymm hsub1 hCz_sub
  -- ## Step E: the image of γ is compact
  have hrange_compact : IsCompact (Set.range γ) := by
    haveI : CompactSpace ↥{z : Fin m → ℝ | V z = 0} := isCompact_iff_compactSpace.mp hC
    rw [hrange_eq, connectedComponentIn_eq_image (F := {z : Fin m → ℝ | V z = 0}) (x := z) hz]
    exact ((isClosed_connectedComponent (x := (⟨z, hz⟩ : ↥{z : Fin m → ℝ | V z = 0}))).isCompact).image
      continuous_subtype_val
  -- ## Step F: γ cannot be injective
  have hnotinj : ¬ Function.Injective γ := by
    intro hinj
    obtain ⟨a, haR, φ, hφmono, hφtend⟩ :=
      hrange_compact.tendsto_subseq (x := fun n : ℕ => γ n) (fun n => ⟨n, rfl⟩)
    obtain ⟨t, ht⟩ := haR
    have haF : V a = 0 := by rw [← ht]; exact hγV t
    obtain ⟨U, ε, hUo, haU, hε, hU⟩ := local_orbit_covers_eps V X hV hX hgrad hX0 htan a haF
    have hsh0 : (fun u => γ (u + t)) 0 = a := by simp [ht]
    have hshd : ∀ u, HasDerivAt (fun u => γ (u + t)) (X ((fun u => γ (u + t)) u)) u :=
      fun u => (hγder (u + t)).comp_add_const u t
    have hcov := hU (fun u => γ (u + t)) hsh0 hshd
    have hev : ∀ᶠ n in Filter.atTop, γ (φ n) ∈ U := hφtend.eventually (hUo.mem_nhds haU)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    have hev2 : ∀ᶠ n in Filter.atTop, t + ε < (φ n : ℝ) := by
      have hthr : ∀ᶠ n in Filter.atTop, ⌈t + ε⌉₊ + 1 < φ n :=
        hφmono.tendsto_atTop.eventually (Filter.eventually_gt_atTop (⌈t + ε⌉₊ + 1))
      filter_upwards [hthr] with n hn
      have h1 : ((⌈t + ε⌉₊ : ℝ) : ℝ) < (φ n : ℝ) := by
        exact_mod_cast (Nat.lt_of_succ_lt hn)
      have h2 : t + ε ≤ (⌈t + ε⌉₊ : ℝ) := Nat.le_ceil _
      linarith
    obtain ⟨N', hN'⟩ := Filter.eventually_atTop.mp hev2
    have hmem : γ (φ (max N N')) ∈ U ∩ {z | V z = 0} :=
      ⟨hN _ (le_max_left _ _), hγV _⟩
    obtain ⟨s, hs, hseq⟩ := hcov hmem
    have hst : s + t = (φ (max N N') : ℝ) := hinj hseq
    have hlt : (φ (max N N') : ℝ) < t + ε := by linarith [hs.2, hst]
    have hgt : t + ε < (φ (max N N') : ℝ) := hN' (max N N') (le_max_right N N')
    linarith
  -- ## Assembly
  unfold Function.Injective at hnotinj
  push_neg at hnotinj
  obtain ⟨a, b, heq, hne⟩ := hnotinj
  refine ⟨|a - b|, γ, ?_, hγ0, hγder, hγV, ?_, hrange_eq⟩
  · rw [abs_pos]; exact sub_ne_zero.mpr hne
  · intro u
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hT : |a - b| = b - a := by rw [abs_of_neg (by linarith), neg_sub]
      rw [hT]
      have hshift : (fun u => γ (u + (b - a))) = γ := by
        apply integral_curve_unique X hX
        · intro u; exact (hγder (u + (b - a))).comp_add_const u (b - a)
        · exact hγder
        · show γ (a + (b - a)) = γ a
          rw [show a + (b - a) = b by ring, heq]
      exact congrFun hshift u
    · have hT : |a - b| = a - b := by rw [abs_of_pos (by linarith)]
      rw [hT]
      have hshift : (fun u => γ (u + (a - b))) = γ := by
        apply integral_curve_unique X hX
        · intro u; exact (hγder (u + (a - b))).comp_add_const u (a - b)
        · exact hγder
        · show γ (b + (a - b)) = γ b
          rw [show b + (a - b) = a by ring, heq]
      exact congrFun hshift u

end Work.WilE2
