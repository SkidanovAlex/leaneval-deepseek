import Mathlib
import Submission.Work.WilE7.DecompDefs
import Submission.Work.WilE7.star_central

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.CoreStep

open WilkiesDesign WilkiesDesign.E

/-! ## A finite relatively-closed cover of a preconnected set

If a preconnected set `c` is covered by a finite family of sets `V i` that are closed in `c`, and
two members meet only when they are equal, then one member already covers `c`. -/
theorem cover_eq_of_preconnected {X : Type*} [TopologicalSpace X] {c : Set X}
    (hc : IsPreconnected c) {ι : Type*} [Finite ι] (V : ι → Set X) (hne : c.Nonempty)
    (hcl : ∀ i, IsClosed (((fun y : c => (y : X)) ⁻¹' (V i) : Set c)))
    (hcover : c ⊆ ⋃ i, V i)
    (hpair : ∀ i j, (V i ∩ V j).Nonempty → V i = V j) :
    ∃ i, c ⊆ V i := by
  haveI : PreconnectedSpace c := isPreconnected_iff_preconnectedSpace.mp hc
  obtain ⟨x₀, hx₀c⟩ := hne
  have hx₀cov : x₀ ∈ ⋃ i, V i := hcover hx₀c
  rw [Set.mem_iUnion] at hx₀cov
  obtain ⟨i₀, hi₀⟩ := hx₀cov
  refine ⟨i₀, ?_⟩
  let u : Set c := {y | (y : X) ∈ V i₀}
  let W : ι → Set c := fun i => {y | (y : X) ∈ V i ∧ (y : X) ∉ V i₀}
  have hWi : ∀ i, IsClosed (W i) := by
    intro i
    by_cases h : V i = V i₀
    · have he : W i = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro y hy
        simp only [W, Set.mem_ofPred_eq] at hy
        exact hy.2 (h ▸ hy.1)
      rw [he]; exact isClosed_empty
    · have he : W i = {y : c | (y : X) ∈ V i} := by
        ext y
        simp only [W, Set.mem_ofPred_eq]
        exact ⟨fun hh => hh.1, fun h1 => ⟨h1, fun h2 => h (hpair i i₀ ⟨(y : X), h1, h2⟩)⟩⟩
      rw [he]; exact hcl i
  have huclosed : IsClosed u := hcl i₀
  have huc_closed : IsClosed (uᶜ) := by
    have he : uᶜ = ⋃ i, W i := by
      ext y
      simp only [Set.mem_compl_iff, u, Set.mem_ofPred_eq, Set.mem_iUnion, W]
      exact ⟨fun hy => by
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover y.2)
        exact ⟨i, hi, hy⟩, fun ⟨i, h1, h2⟩ h3 => h2 h3⟩
    rw [he]
    exact isClosed_iUnion_of_finite hWi
  have huopen : IsOpen u := isClosed_compl_iff.mp huc_closed
  have hune : u.Nonempty := ⟨⟨x₀, hx₀c⟩, hi₀⟩
  have hsub : (Set.univ : Set c) ⊆ u := by
    rcases disjoint_or_subset_of_isClopen (s := (Set.univ : Set c)) (t := u)
        isPreconnected_univ ⟨huclosed, huopen⟩ with hd | hsub
    · exfalso
      obtain ⟨y, hy⟩ := hune
      exact (Set.disjoint_left.mp hd (Set.mem_univ y)) hy
    · exact hsub
  intro x hx
  exact hsub (Set.mem_univ ⟨x, hx⟩)

/-! ## Pinning a continuous function to one member of a dichotomic family

If a continuous `φ : X → ℝ` on a preconnected `c` is, at each point of `c`, equal to one of a
finite family `ψ i` whose members are pairwise "equal on `c` or nowhere equal on `c`", then `φ`
agrees with a single `ψ i` on all of `c`. -/
theorem pinned_of_preconnected {X : Type*} [TopologicalSpace X] {c : Set X}
    (hc : IsPreconnected c) {ι : Type*} [Finite ι] (φ : X → ℝ) (ψ : ι → X → ℝ)
    (hφ : ContinuousOn φ c) (hψ : ∀ i, ContinuousOn (ψ i) c)
    (hdich : ∀ i i', (∃ x ∈ c, ψ i x = ψ i' x) → ∀ x ∈ c, ψ i x = ψ i' x)
    (hcover : ∀ x ∈ c, ∃ i, φ x = ψ i x) (hne : c.Nonempty) :
    ∃ i, ∀ x ∈ c, φ x = ψ i x := by
  have hcl : ∀ i, IsClosed (((fun y : c => (y : X)) ⁻¹' (c ∩ {x | φ x = ψ i x}) : Set c)) := by
    intro i
    have h1 : Continuous fun y : c => φ (y : X) :=
      hφ.comp_continuous continuous_subtype_val (fun y => y.2)
    have h2 : Continuous fun y : c => ψ i (y : X) :=
      (hψ i).comp_continuous continuous_subtype_val (fun y => y.2)
    have heq : (((fun y : c => (y : X)) ⁻¹' (c ∩ {x | φ x = ψ i x}) : Set c))
        = {y : c | φ (y : X) = ψ i (y : X)} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩
    rw [heq]; exact isClosed_eq h1 h2
  have hcov : c ⊆ ⋃ i, (c ∩ {x | φ x = ψ i x}) := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    exact Set.mem_iUnion.mpr ⟨i, hx, hi⟩
  have hpr : ∀ i j, ((c ∩ {x | φ x = ψ i x}) ∩ (c ∩ {x | φ x = ψ j x})).Nonempty →
      (c ∩ {x | φ x = ψ i x}) = (c ∩ {x | φ x = ψ j x}) := by
    intro i j hij
    obtain ⟨y, hy⟩ := hij
    have hyc : y ∈ c := hy.1.1
    have heq : ψ i y = ψ j y := by rw [← hy.1.2, hy.2.2]
    have hd := hdich i j ⟨y, hyc, heq⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨h.1, by rw [h.2, hd x h.1]⟩,
      fun h => ⟨h.1, by rw [h.2, (hd x h.1).symm]⟩⟩
  obtain ⟨i₀, hsub⟩ := cover_eq_of_preconnected hc (fun i => c ∩ {x | φ x = ψ i x}) hne
    hcl hcov hpr
  exact ⟨i₀, fun x hx => (hsub hx).2⟩

/-! ## The engine: upgrading the weak compatibility to a per-index compatibility -/

theorem compat_engine {p r : ℕ} {C : Set (Fin p → ℝ)} {C' : Finset (Set (Fin (p + 1) → ℝ))}
    (hcyl : IsCylDecompOn (p + 1) (Work.WilE7.cyl C) C')
    (k : Fin r → ℕ) (f : (t : Fin r) → Fin (k t) → (Fin p → ℝ) → ℝ)
    (hcont : ∀ (t : Fin r) (j : Fin (k t)), ContinuousOn (f t j) C)
    (hdich : ∀ (t t' : Fin r) (j : Fin (k t)) (j' : Fin (k t')),
      (∃ x ∈ C, f t j x = f t' j' x) → ∀ x ∈ C, f t j x = f t' j' x)
    (hweak : ∀ κ ∈ C', (∃ t : Fin r, κ ⊆ ⋃ j : Fin (k t), Work.WilE7.gr C (f t j)) ∨
      (∀ t : Fin r, Disjoint κ (⋃ j : Fin (k t), Work.WilE7.gr C (f t j)))) :
    ∀ κ ∈ C', ∀ t : Fin r, κ ⊆ (⋃ j : Fin (k t), Work.WilE7.gr C (f t j)) ∨
      Disjoint κ (⋃ j : Fin (k t), Work.WilE7.gr C (f t j)) := by
  intro κ hκ t
  rcases hweak κ hκ with ⟨u, hu⟩ | hdisj
  · by_cases hdt : Disjoint κ (⋃ j : Fin (k t), Work.WilE7.gr C (f t j))
    · exact Or.inr hdt
    · refine Or.inl ?_
      obtain ⟨z₀, hz₀κ, hz₀G⟩ := Set.not_disjoint_iff.mp hdt
      obtain ⟨hcell, hneκ⟩ := hcyl.1 κ hκ
      have key : ∀ (X : Set (Fin (p + 1) → ℝ)), IsCell (p + 1) X → X.Nonempty →
          X ⊆ (⋃ j : Fin (k u), Work.WilE7.gr C (f u j)) →
          (X ∩ (⋃ j : Fin (k t), Work.WilE7.gr C (f t j))).Nonempty →
          X ⊆ (⋃ j : Fin (k t), Work.WilE7.gr C (f t j)) := by
        intro X hX hXne hXu hXt
        cases hX with
        | graph hc g hg =>
          rename_i cc
          have hccC : cc ⊆ C := by
            intro x hx
            have hz : Fin.snoc x (g x) ∈
                ({z : Fin (p + 1) → ℝ | Fin.init z ∈ cc ∧ z (Fin.last p) = g (Fin.init z)} :
                  Set (Fin (p + 1) → ℝ)) := by
              refine ⟨?_, ?_⟩
              · simpa [Fin.init_snoc] using hx
              · simp [Fin.snoc_last]
            obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hXu hz)
            exact by simpa [Fin.init_snoc] using hj.1
          have hpre : IsPreconnected cc := Work.WilE7.isPreconnected_of_isCell hc
          have hnecc : cc.Nonempty := by
            obtain ⟨z, hz⟩ := hXne
            exact ⟨Fin.init z, hz.1⟩
          have hpinned : ∃ i : Fin (k u), ∀ x ∈ cc, g x = f u i x :=
            pinned_of_preconnected hpre g (fun i => f u i) hg
              (fun i => (hcont u i).mono hccC)
              (fun i i' h => by
                obtain ⟨x, hx, heq⟩ := h
                exact fun y hy => hdich u u i i' ⟨x, hccC hx, heq⟩ y (hccC hy))
              (fun x hx => by
                have hz : Fin.snoc x (g x) ∈
                    ({z : Fin (p + 1) → ℝ | Fin.init z ∈ cc ∧ z (Fin.last p) = g (Fin.init z)} :
                      Set (Fin (p + 1) → ℝ)) := by
                  refine ⟨?_, ?_⟩
                  · simpa [Fin.init_snoc] using hx
                  · simp [Fin.snoc_last]
                obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hXu hz)
                exact ⟨i, by simpa [Fin.init_snoc, Fin.snoc_last] using hi.2⟩)
              hnecc
          obtain ⟨i₀, hi₀⟩ := hpinned
          obtain ⟨z₁, hz₁X⟩ := hXt
          obtain ⟨j₁, hj₁⟩ := Set.mem_iUnion.mp hz₁X.2
          have hyeq : f u i₀ (Fin.init z₁) = f t j₁ (Fin.init z₁) :=
            (hi₀ (Fin.init z₁) hz₁X.1.1).symm.trans (hz₁X.1.2.symm.trans hj₁.2)
          have hcv : ∀ x ∈ C, f u i₀ x = f t j₁ x :=
            hdich u t i₀ j₁ ⟨Fin.init z₁, hccC hz₁X.1.1, hyeq⟩
          intro z hz
          exact Set.mem_iUnion.mpr ⟨j₁, hccC hz.1,
            by rw [hz.2, hi₀ (Fin.init z) hz.1, hcv (Fin.init z) (hccC hz.1)]⟩
        | band hc a b ha hb hab =>
          rename_i cc
          obtain ⟨z₀, hz₀⟩ := hXne
          have hx₀cc : Fin.init z₀ ∈ cc := hz₀.1
          have hab₀ : a (Fin.init z₀) < b (Fin.init z₀) := hab _ hx₀cc
          obtain ⟨r, hr1, hr2⟩ := EReal.exists_between_coe_real hab₀
          obtain ⟨r', hr1', hr2'⟩ := EReal.exists_between_coe_real hr2
          have hrr' : r < r' := EReal.coe_lt_coe_iff.mp hr1'
          have hYinf : ({s : ℝ | a (Fin.init z₀) < (s : EReal) ∧
              (s : EReal) < b (Fin.init z₀)} : Set ℝ).Infinite := by
            refine (Set.Ioo_infinite hrr').mono ?_
            intro s hs
            simp only [Set.mem_Ioo] at hs
            exact ⟨lt_trans hr1 (by exact_mod_cast hs.1),
              lt_trans (by exact_mod_cast hs.2) hr2'⟩
          have hYfin : ({s : ℝ | a (Fin.init z₀) < (s : EReal) ∧
              (s : EReal) < b (Fin.init z₀)} : Set ℝ).Finite := by
            refine (Set.finite_range (fun i : Fin (k u) => f u i (Fin.init z₀))).subset ?_
            intro s hs
            have hz : Fin.snoc (Fin.init z₀) s ∈
                ({z : Fin (p + 1) → ℝ | Fin.init z ∈ cc ∧
                  a (Fin.init z) < ((z (Fin.last p) : ℝ) : EReal) ∧
                  ((z (Fin.last p) : ℝ) : EReal) < b (Fin.init z)} :
                    Set (Fin (p + 1) → ℝ)) := by
              refine ⟨?_, ?_, ?_⟩
              · simpa [Fin.init_snoc] using hx₀cc
              · simpa [Fin.init_snoc, Fin.snoc_last] using hs.1
              · simpa [Fin.init_snoc, Fin.snoc_last] using hs.2
            obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hXu hz)
            exact ⟨i, by simpa [Fin.init_snoc, Fin.snoc_last] using hi.2.symm⟩
          exact absurd hYinf (Set.not_infinite.mpr hYfin)
      exact key κ hcell hneκ hu ⟨z₀, hz₀κ, hz₀G⟩
  · exact Or.inr (hdisj t)

/-! ## The requested lemma -/

theorem gcase_compat_strong {p m r : ℕ} {C : Set (Fin p → ℝ)}
    {C' : Finset (Set (Fin (p + 1) → ℝ))}
    (hcyl : WilkiesDesign.E.IsCylDecompOn (p + 1) (Work.WilE7.cyl C) C')
    (k : Fin r → ℕ) (s : (t : Fin r) → Fin (k t) → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ (t : Fin r) (j : Fin (k t)), ContinuousOn (s t j) C)
    (hinj : ∀ (t : Fin r), ∀ x ∈ C, Function.Injective fun j : Fin (k t) => s t j x)
    (hdich : ∀ (t t' : Fin r) (j : Fin (k t)) (j' : Fin (k t')),
      (∃ x ∈ C, s t j x (Fin.last m) = s t' j' x (Fin.last m)) →
        ∀ x ∈ C, s t j x (Fin.last m) = s t' j' x (Fin.last m))
    (hweak : ∀ κ ∈ C', (∃ t : Fin r, κ ⊆ ⋃ j : Fin (k t), {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = (s t j (Fin.init y)) (Fin.last m)}) ∨
      (∀ t : Fin r, Disjoint κ (⋃ j : Fin (k t), {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = (s t j (Fin.init y)) (Fin.last m)}))) :
    ∀ κ ∈ C', ∀ t : Fin r, κ ⊆ (⋃ j : Fin (k t), {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = (s t j (Fin.init y)) (Fin.last m)}) ∨ Disjoint κ (⋃ j : Fin (k t), {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = (s t j (Fin.init y)) (Fin.last m)}) := by
  refine compat_engine hcyl k (fun t j x => s t j x (Fin.last m)) ?_ ?_ ?_
  · intro t j
    exact (continuous_apply (Fin.last m)).comp_continuousOn (hcont t j)
  · intro t t' j j' h
    exact hdich t t' j j' h
  · intro κ hκ
    rcases hweak κ hκ with ⟨t, ht⟩ | h
    · exact Or.inl ⟨t, ht⟩
    · exact Or.inr h

end Work.WilE7.CoreStep
