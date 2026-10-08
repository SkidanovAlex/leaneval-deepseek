import Submission.Work.Coherence.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Basic API for `ℤ[S]`, `ℤ[S]^0`, virtual characters and orthonormal sets

The lemmas here are the interface through which everything else in the coherence area is proved:
the coefficient description of `ℤ[S]`, monotonicity, the description of `ℤ[S]^0` by a degree
condition on the coefficients, the basic closure properties of virtual characters, the
coefficient-extraction lemma for orthonormal sets, and the resulting formula for `cfInner` of two
elements of a lattice spanned by an orthonormal set.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Classical

namespace Work.Coherence

universe u

variable {G : Type*}

section ZSpan

variable [Group G] [Fintype G]

theorem mem_zSpan {S : Finset (G → ℂ)} {f : G → ℂ} :
    f ∈ ZSpan S ↔ ∃ c : S → ℤ, f = ∑ x : S, (c x : ℂ) • (x : G → ℂ) := Iff.rfl

theorem self_mem_zSpan {S : Finset (G → ℂ)} {x : G → ℂ} (hx : x ∈ S) : x ∈ ZSpan S := by
  refine ⟨fun y => if y = ⟨x, hx⟩ then 1 else 0, ?_⟩
  rw [Finset.sum_eq_single (⟨x, hx⟩ : S)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem zSpan_eq_closure (S : Finset (G → ℂ)) :
    ZSpan S = AddSubgroup.closure (↑S : Set (G → ℂ)) := by
  refine le_antisymm ?_ ?_
  · rintro f ⟨c, rfl⟩
    exact AddSubgroup.sum_mem _ fun x _ => by
      rw [Int.cast_smul_eq_zsmul]
      exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure x.2) _
  · rw [AddSubgroup.closure_le]
    exact fun x hx => self_mem_zSpan hx

theorem zSpan_le_iff {S : Finset (G → ℂ)} {K : AddSubgroup (G → ℂ)} :
    ZSpan S ≤ K ↔ (↑S : Set (G → ℂ)) ⊆ K := by
  rw [zSpan_eq_closure]
  exact AddSubgroup.closure_le K

theorem zSpan_mono {S T : Finset (G → ℂ)} (h : S ⊆ T) : ZSpan S ≤ ZSpan T := by
  rw [zSpan_le_iff]
  exact fun x hx => self_mem_zSpan (h hx)

@[simp] theorem zSpan_empty : ZSpan (∅ : Finset (G → ℂ)) = ⊥ := by
  rw [zSpan_eq_closure]
  simp

theorem zSpan_singleton (x : G → ℂ) : ZSpan {x} = AddSubgroup.closure ({x} : Set (G → ℂ)) := by
  rw [zSpan_eq_closure]
  simp

theorem zSpan_union (S T : Finset (G → ℂ)) : ZSpan (S ∪ T) = ZSpan S ⊔ ZSpan T := by
  refine le_antisymm ?_ ?_
  · rw [zSpan_le_iff]
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact AddSubgroup.mem_sup_left (self_mem_zSpan h)
    · exact AddSubgroup.mem_sup_right (self_mem_zSpan h)
  · exact sup_le (zSpan_mono Finset.subset_union_left) (zSpan_mono Finset.subset_union_right)

theorem zSpan0_le_zSpan (S : Finset (G → ℂ)) : ZSpan0 S ≤ ZSpan S := inf_le_left

theorem zSpan0_zero {S : Finset (G → ℂ)} {f : G → ℂ} (hf : f ∈ ZSpan0 S) : f 1 = 0 := hf.2

theorem zSpan0_mono {S T : Finset (G → ℂ)} (h : S ⊆ T) : ZSpan0 S ≤ ZSpan0 T :=
  le_inf (le_trans inf_le_left (zSpan_mono h)) inf_le_right

theorem sum_coeff_apply {S : Finset (G → ℂ)} (c : S → ℤ) (g : G) :
    (∑ x : S, (c x : ℂ) • (x : G → ℂ)) g = ∑ x : S, (c x : ℂ) * (x : G → ℂ) g := by
  simp [Finset.sum_apply, smul_eq_mul]

theorem mem_zSpan0_iff_coeff {S : Finset (G → ℂ)} {f : G → ℂ} :
    f ∈ ZSpan0 S ↔ ∃ c : S → ℤ, f = ∑ x : S, (c x : ℂ) • (x : G → ℂ) ∧
      ∑ x : S, (c x : ℂ) * (x : G → ℂ) 1 = 0 := by
  rw [mem_zSpan0]
  constructor
  · rintro ⟨⟨c, rfl⟩, h0⟩
    exact ⟨c, rfl, by rwa [sum_coeff_apply] at h0⟩
  · rintro ⟨c, rfl, h0⟩
    exact ⟨⟨c, rfl⟩, by rwa [sum_coeff_apply]⟩

end ZSpan

section VChar

variable [Group G] [Fintype G]

/-- Irreducible characters are class functions. -/
theorem isClassFun_of_mem_Irr {χ : G → ℂ} (hχ : χ ∈ Irr G) : IsClassFun χ := by
  obtain ⟨V, -, rfl⟩ := hχ
  exact fun g h => FDRep.char_conj V g h

/-- Characters are virtual characters. -/
theorem IsChar.toIsVChar {f : G → ℂ} (hf : IsChar f) : IsVChar f :=
  AddSubmonoid.closure_le.mpr (fun _ hx => AddSubgroup.subset_closure hx) hf

theorem IsChar.add {f g : G → ℂ} (hf : IsChar f) (hg : IsChar g) : IsChar (f + g) :=
  AddSubmonoid.add_mem _ hf hg

theorem IsChar.zero : IsChar (0 : G → ℂ) := AddSubmonoid.zero_mem _

theorem IsChar.sum {ι : Type*} (s : Finset ι) (F : ι → G → ℂ)
    (h : ∀ i ∈ s, IsChar (F i)) : IsChar (∑ i ∈ s, F i) := AddSubmonoid.sum_mem _ h

/-- Virtual characters are class functions. -/
theorem IsVChar.isClassFun {f : G → ℂ} (hf : IsVChar f) : IsClassFun f := by
  refine AddSubgroup.closure_induction (p := fun f _ => IsClassFun f) ?_ ?_ ?_ ?_ hf
  · intro x hx; exact isClassFun_of_mem_Irr hx
  · exact isClassFun_zero
  · intro x y _ _ hx hy; exact hx.add hy
  · intro x _ hx; exact hx.neg

theorem isVChar_iff {f : G → ℂ} :
    IsVChar f ↔ ∃ s : Finset (G → ℂ), (↑s : Set (G → ℂ)) ⊆ Irr G ∧ f ∈ ZSpan s := by
  constructor
  · intro hf
    refine AddSubgroup.closure_induction
      (p := fun f _ => ∃ s : Finset (G → ℂ), (↑s : Set (G → ℂ)) ⊆ Irr G ∧ f ∈ ZSpan s)
      ?_ ?_ ?_ ?_ hf
    · intro x hx
      refine ⟨{x}, ?_, self_mem_zSpan (by simp)⟩
      intro z hz
      rw [Finset.mem_coe, Finset.mem_singleton] at hz
      rwa [hz]
    · exact ⟨∅, by simp, by simp⟩
    · rintro x y _ _ ⟨s, hs, hxs⟩ ⟨t, ht, hyt⟩
      refine ⟨s ∪ t, ?_, ?_⟩
      · intro z hz
        rcases Finset.mem_union.mp hz with h | h
        · exact hs h
        · exact ht h
      · exact AddSubgroup.add_mem _
          (zSpan_mono Finset.subset_union_left hxs) (zSpan_mono Finset.subset_union_right hyt)
    · rintro x _ ⟨s, hs, hxs⟩
      exact ⟨s, hs, AddSubgroup.neg_mem _ hxs⟩
  · rintro ⟨s, hs, hfs⟩
    exact zSpan_le_iff.mpr (fun x hx => AddSubgroup.subset_closure (hs hx)) hfs

theorem isVChar_of_mem_Irr {f : G → ℂ} (hf : f ∈ Irr G) : IsVChar f :=
  AddSubgroup.subset_closure hf

theorem IsVChar.add {f g : G → ℂ} (hf : IsVChar f) (hg : IsVChar g) : IsVChar (f + g) :=
  AddSubgroup.add_mem _ hf hg

theorem IsVChar.neg {f : G → ℂ} (hf : IsVChar f) : IsVChar (-f) := AddSubgroup.neg_mem _ hf

theorem IsVChar.sub {f g : G → ℂ} (hf : IsVChar f) (hg : IsVChar g) : IsVChar (f - g) :=
  AddSubgroup.sub_mem _ hf hg

theorem IsVChar.zero : IsVChar (0 : G → ℂ) := AddSubgroup.zero_mem _

theorem IsVChar.zsmul {f : G → ℂ} (hf : IsVChar f) (n : ℤ) : IsVChar (n • f) :=
  AddSubgroup.zsmul_mem _ hf n

theorem IsVChar.sum {ι : Type*} (s : Finset ι) (F : ι → G → ℂ)
    (h : ∀ i ∈ s, IsVChar (F i)) : IsVChar (∑ i ∈ s, F i) :=
  AddSubgroup.sum_mem _ h

theorem isVChar_iff_coeff {f : G → ℂ} :
    IsVChar f ↔ ∃ s : Finset (G → ℂ), (↑s : Set (G → ℂ)) ⊆ Irr G ∧
      ∃ c : s → ℤ, f = ∑ x : s, (c x : ℂ) • (x : G → ℂ) := by
  rw [isVChar_iff]
  constructor
  · rintro ⟨s, hs, hfs⟩
    exact ⟨s, hs, mem_zSpan.mp hfs⟩
  · rintro ⟨s, hs, c, hc⟩
    exact ⟨s, hs, mem_zSpan.mpr ⟨c, hc⟩⟩

theorem isChar_of_isVChar_coeff {f : G → ℂ} {s : Finset (G → ℂ)}
    (hs : (↑s : Set (G → ℂ)) ⊆ Irr G) {c : s → ℕ}
    (hf : f = ∑ x : s, (c x : ℂ) • (x : G → ℂ)) : IsVChar f :=
  (isVChar_iff_coeff).mpr ⟨s, hs, fun x => (c x : ℤ), by
    rw [hf]; exact Finset.sum_congr rfl fun x _ => by norm_num⟩

end VChar

section Orthonormal

variable [Group G] [Fintype G]

theorem orthonormal_iff {S : Finset (G → ℂ)} :
    Orthonormal S ↔ ∀ x ∈ S, ∀ y ∈ S, cfInner x y = if x = y then 1 else 0 := Iff.rfl

theorem Orthonormal.mono {S T : Finset (G → ℂ)} (h : Orthonormal T) (hST : S ⊆ T) :
    Orthonormal S := fun x hx y hy => h x (hST hx) y (hST hy)

theorem Orthonormal.cfInner_self {S : Finset (G → ℂ)} (h : Orthonormal S) {x : G → ℂ}
    (hx : x ∈ S) : cfInner x x = 1 := by
  rw [h x hx x hx]; simp

theorem Orthonormal.cfInner_eq_zero {S : Finset (G → ℂ)} (h : Orthonormal S) {x y : G → ℂ}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) : cfInner x y = 0 := by
  rw [h x hx y hy]; simp [hxy]

end Orthonormal

section Coeff

variable [Group G] [Fintype G]

/-- **Coefficient extraction.**  If `S` is orthonormal and `α ∈ ℤ[S]` is written as an integral
combination `∑ c x • x`, then `c x = ⟨α, x⟩`. -/
theorem cfInner_eq_coeff {S : Finset (G → ℂ)} (hS : Orthonormal S) {α : G → ℂ} {c : S → ℤ}
    (hα : α = ∑ x : S, (c x : ℂ) • (x : G → ℂ)) (y : S) : cfInner α y = (c y : ℂ) := by
  subst hα
  rw [cfInner_sum_left, Finset.sum_eq_single y]
  · rw [cfInner_smul_left, hS _ y.2 _ y.2]; simp
  · intro b _ hb
    rw [cfInner_smul_left]
    have hne : (b : G → ℂ) ≠ (y : G → ℂ) := fun h => hb (Subtype.ext h)
    rw [hS _ b.2 _ y.2]; simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Coefficients of an element of `ℤ[S]` with respect to an orthonormal set are integers. -/
theorem exists_int_coeff {S : Finset (G → ℂ)} (hS : Orthonormal S) {α : G → ℂ}
    (hα : α ∈ ZSpan S) (x : S) : ∃ n : ℤ, cfInner α (x : G → ℂ) = (n : ℂ) := by
  obtain ⟨c, hc⟩ := mem_zSpan.mp hα
  exact ⟨c x, cfInner_eq_coeff hS hc x⟩

/-- **Reconstruction.**  With respect to an orthonormal set, every element of `ℤ[S]` is the
integral combination of the elements of `S` with the coefficients `⟨α, x⟩`. -/
theorem eq_sum_coeff {S : Finset (G → ℂ)} (hS : Orthonormal S) {α : G → ℂ}
    (hα : α ∈ ZSpan S) :
    α = ∑ x : S, (cfInner α (x : G → ℂ)) • (x : G → ℂ) := by
  obtain ⟨c, hc⟩ := mem_zSpan.mp hα
  subst hc
  exact Finset.sum_congr rfl fun x _ => by rw [cfInner_eq_coeff hS rfl x]

/-- The inner product of two elements of a lattice spanned by an orthonormal set, in terms of
their integral coordinates. -/
theorem cfInner_eq_sum_coeff_mul {S : Finset (G → ℂ)} (hS : Orthonormal S) {f g : G → ℂ}
    {c d : S → ℤ} (hf : f = ∑ x : S, (c x : ℂ) • (x : G → ℂ))
    (hg : g = ∑ x : S, (d x : ℂ) • (x : G → ℂ)) :
    cfInner f g = ∑ x : S, (c x : ℂ) * (d x : ℂ) := by
  subst hf
  rw [cfInner_sum_left]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [cfInner_smul_left, cfInner_conj_symm, cfInner_eq_coeff hS hg x]
  simp

/-- **Norm formula.**  If `f ∈ ℤ[S]` for an orthonormal `S` with coordinates `c`, then
`⟨f, f⟩ = ∑ c x ^ 2`.  In particular `⟨f,f⟩` is a non-negative integer. -/
theorem cfInner_self_eq_sum_sq {S : Finset (G → ℂ)} (hS : Orthonormal S) {f : G → ℂ}
    {c : S → ℤ} (hf : f = ∑ x : S, (c x : ℂ) • (x : G → ℂ)) :
    cfInner f f = ∑ x : S, ((c x : ℤ) : ℂ) ^ 2 := by
  rw [cfInner_eq_sum_coeff_mul hS hf hf]
  exact Finset.sum_congr rfl fun x _ => by ring

end Coeff

end Work.Coherence
