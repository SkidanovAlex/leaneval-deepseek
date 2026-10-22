import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.ZS.Level

namespace Work.ATOM

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

/-!
# The level structure of `S` and the enumeration of `D'`

This file proves `Work.ATOM.exists_level_enumeration`.  Everything is built on the tower
`S.component n` / `S.proj n` of Mathlib and on the maps `sig`, `e` of
`Submission/Work/ATOM/ZS/Level.lean`.
-/

section Tower

variable (S : LightProfinite.{0})

/-! ## 1.  The iterated transition and section maps, pointwise -/

/-- `itTr` is Mathlib's `transitionMapLE`. -/
lemma itTr_eq_transitionMapLE {n m : ℕ} (h : m ≤ n) :
    itTr S n m h = S.transitionMapLE h := rfl

/-- The projection of the limit cone is compatible with the transition maps. -/
lemma proj_comp_itTr {n m : ℕ} (h : m ≤ n) : S.proj n ≫ itTr S n m h = S.proj m := by
  rw [itTr_eq_transitionMapLE]
  exact S.proj_comp_transitionMapLE h

/-- Pointwise form of `proj_comp_itTr`. -/
lemma proj_comp_itTr_apply {n m : ℕ} (h : m ≤ n) (x : ↥S) :
    itTr S n m h (S.proj n x) = S.proj m x := by
  rw [← CategoryTheory.comp_apply (f := S.proj n) (g := itTr S n m h) (x := x),
    proj_comp_itTr]

/-- Composition of iterated transitions: proved by cancelling the surjective projection `S.proj n`. -/
lemma itTr_comp_general {n m j : ℕ} (h1 : m ≤ n) (h2 : j ≤ m) :
    itTr S n m h1 ≫ itTr S m j h2 = itTr S n j (le_trans h2 h1) := by
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨y, rfl⟩ := S.proj_surjective n x
  rw [CategoryTheory.comp_apply, proj_comp_itTr_apply S h1 y,
    proj_comp_itTr_apply S (le_trans h2 h1) y]
  exact proj_comp_itTr_apply S h2 y

/-- Pointwise form of `itTr_comp_general`. -/
lemma itTr_comp_apply {n m j : ℕ} (h1 : m ≤ n) (h2 : j ≤ m) (t : ↥(S.component n)) :
    itTr S m j h2 (itTr S n m h1 t) = itTr S n j (le_trans h2 h1) t := by
  simpa using ConcreteCategory.congr_hom (itTr_comp_general S h1 h2) t

/-- Composition of iterated sections. -/
lemma itSe_comp {n m k : ℕ} (h1 : n ≤ m) (h2 : m ≤ k) :
    itSe S n m h1 ≫ itSe S m k h2 = itSe S n k (le_trans h1 h2) := by
  induction k, h2 using Nat.le_induction with
  | base => simp [itSe_self]
  | succ k hk ih =>
      rw [itSe_succ S m k hk]
      rw [show itSe S n (k + 1) (le_trans h1 (Nat.le_succ_of_le hk))
            = itSe S n (k + 1) (Nat.le_succ_of_le (le_trans h1 hk)) from
          congrArg (itSe S n (k + 1)) (Subsingleton.elim _ _)]
      rw [itSe_succ S n k (le_trans h1 hk), ← Category.assoc, ih]

/-- Pointwise form of `itSe_comp`. -/
lemma itSe_comp_apply {n m k : ℕ} (h1 : n ≤ m) (h2 : m ≤ k) (t : ↥(S.component n)) :
    itSe S m k h2 (itSe S n m h1 t) = itSe S n k (le_trans h1 h2) t := by
  simpa using ConcreteCategory.congr_hom (itSe_comp S h1 h2) t

/-- The chosen section of the transition map is a section. -/
lemma transitionMap_sect (m : ℕ) (u : ↥(S.component m)) :
    S.transitionMap m (sect S m u) = u := by
  simpa using ConcreteCategory.congr_hom (sect_transitionMap S m) u

/-- The iterated section is a section of the iterated transition. -/
lemma itSe_itTr {j m : ℕ} (h : j ≤ m) : itSe S j m h ≫ itTr S m j h = 𝟙 (S.component j) := by
  induction m, h using Nat.le_induction with
  | base => simp [itSe_self, itTr_self]
  | succ m hm ih =>
      have hfac : itTr S (m + 1) j (Nat.le_succ_of_le hm)
          = S.transitionMap m ≫ itTr S m j hm := by
        rw [show (Nat.le_succ_of_le hm : j ≤ m + 1) = (le_trans hm (Nat.le_succ m)) from
          Subsingleton.elim _ _]
        exact (itTr_comp_general S (Nat.le_succ m) hm).symm
      rw [itSe_succ S j m hm, hfac]
      rw [Category.assoc (f := itSe S j m hm) (g := sect S m)
        (h := S.transitionMap m ≫ itTr S m j hm)]
      rw [← Category.assoc (f := sect S m) (g := S.transitionMap m) (h := itTr S m j hm)]
      rw [sect_transitionMap S m, Category.id_comp, ih]

/-- Pointwise form of `itSe_itTr`. -/
lemma itSe_itTr_apply {j m : ℕ} (h : j ≤ m) (t : ↥(S.component j)) :
    itTr S m j h (itSe S j m h t) = t := by
  simpa using ConcreteCategory.congr_hom (itSe_itTr S h) t

/- Two points of a light profinite set which have the same projection to every finite component
are equal.  (`S.asLimitCone.pt` is only definitionally `S`, so we need the defeq transparency
option to use the limit projections.) -/
set_option backward.isDefEq.respectTransparency false in
lemma proj_separates {x y : ↥S} (h : ∀ n : ℕ, S.proj n x = S.proj n y) : x = y := by
  let f : S ⟶ S := ConcreteCategory.ofHom (ContinuousMap.const (α := ↥S) x)
  let g : S ⟶ S := ConcreteCategory.ofHom (ContinuousMap.const (α := ↥S) y)
  have hfg : f = g := by
    refine S.asLimit.hom_ext (fun j => ?_)
    obtain ⟨n⟩ := j
    apply ConcreteCategory.hom_ext
    intro z
    simp only [f, g, ConcreteCategory.hom_ofHom, ContinuousMap.const_apply]
    exact h n
  simpa [f, g] using ConcreteCategory.congr_hom hfg x

/-- **The key compatibility of `leg` with the iterated sections.** -/
lemma leg_itSe {n m j : ℕ} (h : n ≤ m) (t : ↥(S.component n)) :
    leg S m j (itSe S n m h t) = leg S n j t := by
  rcases le_or_gt j n with hjn | hnj
  · rw [leg_of_le S m j (le_trans hjn h), leg_of_le S n j hjn]
    rw [← itTr_comp_apply (S := S) (h1 := h) (h2 := hjn) (t := itSe S n m h t)]
    rw [itSe_itTr_apply (S := S) (h := h) (t := t)]
  · have hnj' : n ≤ j := le_of_lt hnj
    by_cases hjm : j ≤ m
    · rw [leg_of_le S m j hjm, leg_of_ge S n j hnj']
      rw [show h = (le_trans hnj' hjm : n ≤ m) from Subsingleton.elim _ _]
      rw [← itSe_comp_apply (S := S) (h1 := hnj') (h2 := hjm) (t := t)]
      rw [itSe_itTr_apply (S := S) (h := hjm) (t := itSe S n j hnj' t)]
    · have hmj : m ≤ j := le_of_not_ge hjm
      rw [leg_of_ge S m j hmj, leg_of_ge S n j hnj']
      rw [itSe_comp_apply (S := S) (h1 := h) (h2 := hmj) (t := t)]

/-- **`σ_n` is compatible with the iterated sections**: `A_n ⊆ A_m` for `n ≤ m`. -/
lemma itSe_sig_apply {n m : ℕ} (h : n ≤ m) (t : ↥(S.component n)) :
    sig S m (itSe S n m h t) = sig S n t := by
  apply proj_separates S
  intro j
  rw [proj_sig_apply S m j (itSe S n m h t), proj_sig_apply S n j t]
  exact leg_itSe S h t

/-! ## 2.  The idempotents `e_n` and their images `A_n` -/

/-- The idempotents compose to the idempotent of the smaller index. -/
lemma e_comp (n m : ℕ) : e S n ≫ e S m = e S (min n m) := by
  apply ConcreteCategory.hom_ext
  intro x
  rw [CategoryTheory.comp_apply, e_apply, e_apply, e_apply]
  rw [proj_sig_apply S n m (S.proj n x)]
  rcases le_total n m with hnm | hmn
  · rw [Nat.min_eq_left hnm, leg_of_ge S n m hnm, itSe_sig_apply S hnm]
  · rw [Nat.min_eq_right hmn, leg_of_le S n m hmn]
    rw [proj_comp_itTr_apply S hmn x]

/-- `e_{n+1}` fixes the image of `e_n`. -/
lemma e_succ_comp (n : ℕ) (x : ↥S) : e S (n + 1) (e S n x) = e S n x := by
  have h := ConcreteCategory.congr_hom (e_comp S n (n + 1)) x
  rw [Nat.min_eq_left (Nat.le_succ n)] at h
  simpa only [CategoryTheory.comp_apply] using h

/-- `e_n` fixes the image of `σ_n`. -/
lemma e_fixes_sig (n : ℕ) (t : ↥(S.component n)) : e S n (sig S n t) = sig S n t := by
  rw [e_apply, sig_proj_apply]

/-- `A S n` is exactly the range of `σ_n`. -/
lemma A_eq_range_sig (n : ℕ) : A S n = Set.range (sig S n) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨S.proj n x, (e_apply S n x).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨sig S n t, e_fixes_sig S n t⟩

/-- Membership in `A S n`, in terms of `σ_n`. -/
lemma mem_A_iff_sig (n : ℕ) (y : ↥S) : y ∈ A S n ↔ ∃ t : ↥(S.component n), sig S n t = y := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨S.proj n x, (e_apply S n x).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨sig S n t, e_fixes_sig S n t⟩

/-- `sig S n t ∈ A S n`. -/
lemma sig_mem_A (n : ℕ) (t : ↥(S.component n)) : sig S n t ∈ A S n :=
  (mem_A_iff_sig S n _).mpr ⟨t, rfl⟩

/-- The `A S n` are increasing. -/
lemma A_subset_succ (n : ℕ) : A S n ⊆ A S (n + 1) := by
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  exact ⟨e S n x, e_succ_comp S n x⟩

/-- The chosen base point `σ_0(t₀)` is fixed by every `e_n`. -/
lemma e_base_fixed (t₀ : ↥(S.component 0)) (n : ℕ) : e S n (sig S 0 t₀) = sig S 0 t₀ := by
  rw [e_apply, proj_sig_apply S 0 n t₀, leg_of_ge S 0 n (Nat.zero_le n)]
  exact itSe_sig_apply S (Nat.zero_le n) t₀

/-- `e_n` fixes `A S n`. -/
lemma e_fixes_of_mem_A {n : ℕ} {y : ↥S} (hy : y ∈ A S n) : e S n y = y := by
  obtain ⟨t, ht⟩ := (mem_A_iff_sig S n y).mp hy
  rw [← ht]
  exact e_fixes_sig S n t

end Tower

/-! ## 3.  Finiteness and cardinality of the `A S n` -/

section Counting

variable (S : LightProfinite.{0})

/-- The components of a light profinite set are finite. -/
lemma finite_component (n : ℕ) : Finite ↥(S.component n) := by
  change Finite ↥(S.fintypeDiagram.obj ⟨n⟩)
  infer_instance

/-- `A S n` is finite: it is the image of the finite set `S.component n` under `σ_n`. -/
lemma A_finite (n : ℕ) : (A S n).Finite := by
  rw [A_eq_range_sig]
  haveI := finite_component S n
  have h : ((fun t : ↥(S.component n) => sig S n t) '' (Set.univ : Set ↥(S.component n))).Finite :=
    Set.finite_univ.image (fun t : ↥(S.component n) => sig S n t)
  simpa [Set.image_univ] using h

/-- `A S n` has as many points as `S.component n`. -/
lemma card_A (n : ℕ) : Nat.card ↥(A S n) = Nat.card ↥(S.component n) := by
  have hinj : Function.Injective (fun t : ↥(S.component n) => sig S n t) := by
    intro a b hab
    have h := congrArg (fun z => S.proj n z) hab
    simpa only [sig_proj_apply] using h
  rw [A_eq_range_sig]
  exact (Nat.card_congr (Equiv.ofInjective (fun t : ↥(S.component n) => sig S n t) hinj)).symm

/-! ## 4.  The level function -/

/-- The level of a point of `D = ⋃ A_n`: the least `n` with `y ∈ A_n` (`0` for `y ∉ D`). -/
noncomputable def lv (y : ↥S) : ℕ := sInf {n : ℕ | y ∈ A S n}

lemma lv_mem {y : ↥S} (h : ∃ n, y ∈ A S n) : y ∈ A S (lv S y) :=
  Nat.sInf_mem h

lemma lv_le {y : ↥S} {m : ℕ} (hm : y ∈ A S m) : lv S y ≤ m :=
  Nat.sInf_le hm

/-! ## 5.  Unboundedness of the components -/

/-- A monotone sequence of natural numbers bounded by `N` is eventually constant. -/
lemma monotone_eventually_const {a : ℕ → ℕ} (ha : Monotone a) (N : ℕ) (hN : ∀ n, a n ≤ N) :
    ∃ n₀, ∀ n ≥ n₀, a n = a n₀ := by
  induction N with
  | zero =>
      exact ⟨0, fun n _ => le_antisymm (le_trans (hN n) (Nat.zero_le _))
        (le_trans (hN 0) (Nat.zero_le _))⟩
  | succ N ih =>
      by_cases h : ∃ n, a n = N + 1
      · obtain ⟨n₀, hn₀⟩ := h
        exact ⟨n₀, fun n hn => le_antisymm (hn₀ ▸ hN n) (ha hn)⟩
      · push_neg at h
        exact ih (fun n => by have h1 := hN n; have h2 := h n; omega)

/-- The number of points of the finite components is monotone in the index. -/
lemma card_component_mono {n m : ℕ} (h : n ≤ m) :
    Nat.card ↥(S.component n) ≤ Nat.card ↥(S.component m) := by
  haveI := finite_component S m
  exact Nat.card_le_card_of_surjective (fun x : ↥(S.component m) => S.transitionMapLE h x)
    (S.surjective_transitionMapLE h)

/-- **For an infinite light profinite set the number of points of the finite components is
unbounded.** -/
lemma component_card_unbounded [Infinite S] : ∀ N : ℕ, ∃ n : ℕ, N ≤ Nat.card ↥(S.component n) := by
  by_contra h
  push_neg at h
  obtain ⟨N, hN⟩ := h
  obtain ⟨n₀, hn₀⟩ := monotone_eventually_const (fun _ _ hab => card_component_mono S hab) N
    (fun n => le_of_lt (hN n))
  have hinj : ∀ n (hn : n₀ ≤ n),
      Function.Injective (fun z : ↥(S.component n) => S.transitionMapLE hn z) := by
    intro n hn
    haveI := finite_component S n
    have hsurj : Function.Surjective (fun z : ↥(S.component n) => S.transitionMapLE hn z) :=
      S.surjective_transitionMapLE hn
    have hcard : Nat.card ↥(S.component n₀) = Nat.card ↥(S.component n) := (hn₀ n hn).symm
    have hnc : ((fun z : ↥(S.component n) => S.transitionMapLE hn z) ''
        (Set.univ : Set ↥(S.component n))).ncard
        = (Set.univ : Set ↥(S.component n)).ncard := by
      rw [Set.image_univ, Set.range_eq_univ.mpr hsurj, Set.ncard_univ, Set.ncard_univ, hcard]
    exact Set.injOn_univ.mp ((Set.ncard_image_iff (s := Set.univ)).mp hnc)
  have hprojinj : Function.Injective (fun x : ↥S => S.proj n₀ x) := by
    intro x y hxy
    refine proj_separates S (fun m => ?_)
    rcases le_or_gt m n₀ with hm | hm
    · have h := congrArg (fun z => itTr S n₀ m hm z) hxy
      simpa only [proj_comp_itTr_apply S hm x, proj_comp_itTr_apply S hm y] using h
    · have hm' : n₀ ≤ m := le_of_lt hm
      have hx : S.proj n₀ x = S.transitionMapLE hm' (S.proj m x) := by
        rw [← proj_comp_itTr_apply S hm' x]
        rfl
      have hy : S.proj n₀ y = S.transitionMapLE hm' (S.proj m y) := by
        rw [← proj_comp_itTr_apply S hm' y]
        rfl
      refine hinj m hm' ?_
      calc S.transitionMapLE hm' (S.proj m x) = S.proj n₀ x := hx.symm
        _ = S.proj n₀ y := hxy
        _ = S.transitionMapLE hm' (S.proj m y) := hy
  haveI := finite_component S n₀
  haveI : Finite ↥S := Finite.of_injective (fun x : ↥S => S.proj n₀ x) hprojinj
  exact not_finite ↥S

/-! ## 6.  `D = ⋃ A_n` is countable and infinite -/

lemma D_countable : (⋃ n, A S n).Countable :=
  Set.countable_iUnion (fun n => (A_finite S n).countable)

lemma D_infinite [Infinite S] : (⋃ n, A S n).Infinite := by
  intro hfin
  haveI : Finite ↥(⋃ n, A S n) := hfin.to_subtype
  obtain ⟨n, hn⟩ := component_card_unbounded S (Nat.card ↥(⋃ n, A S n) + 1)
  have h1 : Nat.card ↥(A S n) ≤ Nat.card ↥(⋃ n, A S n) :=
    Nat.card_le_card_of_injective (Set.inclusion (Set.subset_iUnion (fun n => A S n) n))
      (Set.inclusion_injective _)
  have h2 : Nat.card ↥(S.component n) = Nat.card ↥(A S n) := (card_A S n).symm
  omega

end Counting

/-! ## 7.  Enumerating a countably infinite set -/

/-- A countably infinite set can be enumerated by the natural numbers, with an explicit
two-sided inverse. -/
theorem enumeration_of_countable_infinite {α : Type*} (s : Set α) (hs : s.Infinite)
    (hc : s.Countable) :
    ∃ (a : ℕ → α) (idx : α → ℕ),
      Function.Injective a ∧ Set.range a = s ∧ (∀ j : ℕ, idx (a j) = j) ∧
      (∀ y : α, ∀ _ : y ∈ s, a (idx y) = y) := by
  classical
  haveI : Infinite ↥s := hs.to_subtype
  haveI : Countable ↥s := Set.countable_coe_iff.mpr hc
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat ↥s
  obtain ⟨f, hf⟩ := Function.Embedding.schroeder_bernstein
    (f := fun j : ℕ => (Infinite.natEmbedding ↥s) j) (g := g)
    (Infinite.natEmbedding ↥s).injective hg
  let E : ℕ ≃ ↥s := Equiv.ofBijective f hf
  refine ⟨fun j => (E j : α), fun y => if h : y ∈ s then E.symm ⟨y, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact E.injective (Subtype.ext hij)
  · ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact (E j).2
    · intro hy
      exact ⟨E.symm ⟨y, hy⟩, by simp⟩
  · intro j
    show (if h : (E j : α) ∈ s then E.symm ⟨(E j : α), h⟩ else 0) = j
    rw [dite_eq_left (E j).2]
    exact E.symm_apply_apply j
  · intro y hy
    show (E (if h : y ∈ s then E.symm ⟨y, h⟩ else 0) : α) = y
    rw [dite_eq_left hy]
    exact congrArg Subtype.val (E.apply_symm_apply ⟨y, hy⟩)

/-! ## 8.  The main theorem -/

/-- The level structure and the enumeration of `NOTES_LEAD_solid_gaps1.md` §3.1, on top of the
tower `Work.ATOM.sig` / `Work.ATOM.e` of `Submission/Work/ATOM/ZS/Level.lean` (where
`S.component n = S_n`, `S.proj n = π_n`).

`A_n := range (e_n)` is the finite image of the `n`-th idempotent, `D := ⋃_n A_n`, and
`D' := D \ {s₀}` is countably infinite when `S` is infinite.  We ask for the base point `s₀`, the
level function `lv` (with `y ∈ A_{lv y}` and `y ∉ A_m` for `m < lv y`) and a bijection
`a : ℕ ≃ D'` with inverse `idx`.  This is the combinatorial input for the maps `ψ`, `φ_P`, `β` of
§3.1 and for the map `g : P ⟶ ℤ[S]` of §3.2. -/
theorem exists_level_enumeration (S : LightProfinite.{0}) [Infinite S] :
    ∃ (s₀ : ↥S) (lv : ↥S → ℕ) (a : ℕ → ↥S) (idx : ↥S → ℕ),
      (∀ n, Work.ATOM.e S n s₀ = s₀) ∧
      (s₀ ∈ Work.ATOM.A S 0) ∧
      (∀ n, Work.ATOM.A S n ⊆ Work.ATOM.A S (n + 1)) ∧
      (∀ n y, (∃ t : ↥(S.component n), Work.ATOM.sig S n t = y) → Work.ATOM.e S n y = y) ∧
      (∀ n m, Work.ATOM.e S n ≫ Work.ATOM.e S m = Work.ATOM.e S (min n m)) ∧
      (∀ y, y ∈ (⋃ n, Work.ATOM.A S n) → y ∈ Work.ATOM.A S (lv y)) ∧
      (∀ y, y ∈ (⋃ n, Work.ATOM.A S n) → ∀ m, m < lv y → y ∉ Work.ATOM.A S m) ∧
      (Function.Injective a) ∧
      (Set.range a = (⋃ n, Work.ATOM.A S n) \ {s₀}) ∧
      (∀ j : ℕ, idx (a j) = j) ∧
      (∀ y : ↥S, ∀ _ : y ∈ (⋃ n, Work.ATOM.A S n) \ {s₀}, a (idx y) = y) ∧
      (∀ j : ℕ, Work.ATOM.e S (lv (a j)) (a j) = a j) := by
  classical
  obtain ⟨t₀⟩ := Infinite.nonempty ↥S
  let s₀ : ↥S := sig S 0 (S.proj 0 t₀)
  have hs₀ : s₀ = sig S 0 (S.proj 0 t₀) := rfl
  obtain ⟨a, idx, ha_inj, ha_range, hidx1, hidx2⟩ :=
    enumeration_of_countable_infinite ((⋃ n, A S n) \ {s₀})
      ((D_infinite S).sdiff (Set.finite_singleton s₀)) ((D_countable S).mono (Set.sdiff_subset))
  refine ⟨s₀, lv S, a, idx, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ha_inj, ha_range, hidx1, hidx2, ?_⟩
  · intro n
    rw [hs₀]
    exact e_base_fixed S (S.proj 0 t₀) n
  · rw [hs₀]
    exact sig_mem_A S 0 (S.proj 0 t₀)
  · intro n
    exact A_subset_succ S n
  · intro n y hy
    obtain ⟨t, ht⟩ := hy
    rw [← ht]
    exact e_fixes_sig S n t
  · intro n m
    exact e_comp S n m
  · intro y hy
    exact lv_mem S (Set.mem_iUnion.mp hy)
  · intro y hy m hm hym
    have h := lv_le S (y := y) hym
    omega
  · intro j
    have hmem : a j ∈ (⋃ n, A S n) := by
      have h1 : a j ∈ Set.range a := Set.mem_range_self j
      rw [ha_range] at h1
      exact h1.1
    exact e_fixes_of_mem_A S (lv_mem S (Set.mem_iUnion.mp hmem))

end

end Work.ATOM
