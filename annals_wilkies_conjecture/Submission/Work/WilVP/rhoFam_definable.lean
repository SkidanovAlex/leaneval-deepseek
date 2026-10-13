/-
  WilVP/rhoFam_definable : `∅`-definability of the iso-radius family `RhoFam`.

  `RhoFam Y K₀ ⊆ ℝ^{k+2}` (coordinates `(x, ρ, c)`) is the graph of the "iso-radius"
  `ρ_c(x) = inf {r ≥ 0 : r not good}`, where `r` is good at `(x, y₀)` when the open `r`-ball
  around `x` stays in the domain of the `c`-fibre and `|F_c|` stays within the factor `K₀` of
  `|y₀|` (see `Work.WilVP.IsoGood`).

  Strategy.  Put `S ⊆ ℝ^{k+3}` (coordinates `(x, y₀, c, r)`) as
  `Fin.init w ∈ Y ∧ w 1 ≠ 0 ∧ 0 ≤ w (last) ∧ w ∈ notGood`, where `notGood` is the complement of
  `IsoGood` unfolded: `∃ u, |u - x| < r ∧ ∀ y, ¬(graph ∧ |y| ≤ K₀|y₀| ∧ |y₀| ≤ K₀|y|)`.  Every
  conjunct of `S` is `∅`-definable in `LRc`:

  * `Fin.init w ∈ Y` is a reindexing of `Y` (`Set.Definable.preimage_comp`);
  * `w 1 ≠ 0` and `0 ≤ w (last)` are polynomial (in)equalities
    (`Work.WilC4.definable_ne_LRc`, `Work.WilC4.definable_le_LRc`);
  * `notGood` is built from the graph substitution of `Y` and the linear inequalities
    `|a| ≤ K|b| ↔ (0 ≤ b ∧ a ≤ Kb ∧ -a ≤ Kb) ∨ (b ≤ 0 ∧ a ≤ -Kb ∧ -a ≤ -Kb)`
    (the two quantifiers `∃u`, `∀y` over `ℝ` are the *finite* quantifiers over `Fin 1 → ℝ`).

  Then `Work.WilC4.definable_isGLB_family` applied to `S` defines the set of tuples
  `(x, y₀, c, ρ)` with `ρ` the GLB of the bad radii; `Set.Definable.image_comp` along the
  index map `falong : Fin (k+2) → Fin (k+3)` (skipping the `y₀`-slot `1`) does the existential
  quantification of `y₀` and simultaneously reindexes `(x, y₀, c, ρ)` to `(x, ρ, c)`, giving
  `RhoFam` exactly.
-/
import Mathlib
import Submission.Work.WilVP.Defs
import Submission.Work.WilC4.definable_isGLB_family
import Submission.Work.WilC4.crit_def_bad_aux

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc)

namespace Work.WilVP.RhoAux

/-! ## 1. Elementary polynomial-inequality sets -/

theorem definable_univ_iff_empty' {α : Type*} {s : Set (α → ℝ)} :
    (Set.univ : Set ℝ).Definable LRc s ↔ (∅ : Set ℝ).Definable LRc s := by
  refine ⟨fun h => ?_, fun h => h.mono (Set.subset_univ _)⟩
  rw [Set.definable_iff_empty_definable_with_params] at h
  exact h.map_expansion Work.WilC4.univToLRc

theorem definable_le_mul_const {σ : Type*} (i j : σ) (K : ℝ) :
    (∅ : Set ℝ).Definable LRc {g : σ → ℝ | g i ≤ K * g j} := by
  refine definable_univ_iff_empty'.mp ?_
  have h := Work.WilC4.definable_le_LRc (σ := σ)
    (MvPolynomial.X i) (MvPolynomial.C K * MvPolynomial.X j)
  simpa using h

theorem definable_le_const {σ : Type*} (i : σ) (K : ℝ) :
    (∅ : Set ℝ).Definable LRc {g : σ → ℝ | g i ≤ K} := by
  refine definable_univ_iff_empty'.mp ?_
  have h := Work.WilC4.definable_le_LRc (σ := σ) (MvPolynomial.X i) (MvPolynomial.C K)
  simpa using h

theorem definable_const_le {σ : Type*} (K : ℝ) (i : σ) :
    (∅ : Set ℝ).Definable LRc {g : σ → ℝ | K ≤ g i} := by
  refine definable_univ_iff_empty'.mp ?_
  have h := Work.WilC4.definable_le_LRc (σ := σ) (MvPolynomial.C K) (MvPolynomial.X i)
  simpa using h

theorem definable_neg_le_mul_const {σ : Type*} (i j : σ) (K : ℝ) :
    (∅ : Set ℝ).Definable LRc {g : σ → ℝ | -g i ≤ K * g j} := by
  refine definable_univ_iff_empty'.mp ?_
  have h := Work.WilC4.definable_le_LRc (σ := σ)
    (-MvPolynomial.X i) (MvPolynomial.C K * MvPolynomial.X j)
  simpa using h

theorem definable_sub_lt {σ : Type*} (i j l : σ) :
    (∅ : Set ℝ).Definable LRc {g : σ → ℝ | g i - g j < g l} := by
  refine definable_univ_iff_empty'.mp ?_
  have h := Work.WilC4.definable_eval_pos_LRc (σ := σ)
    (MvPolynomial.X l - (MvPolynomial.X i - MvPolynomial.X j))
  simpa [sub_pos] using h

/-! ## 2. `|a| ≤ K * |b|` as a Boolean combination of linear inequalities -/

def absLe (K a b : ℝ) : Prop :=
  (0 ≤ b ∧ a ≤ K * b ∧ -a ≤ K * b) ∨ (b ≤ 0 ∧ a ≤ -K * b ∧ -a ≤ -K * b)

theorem absLe_iff (K a b : ℝ) : absLe K a b ↔ |a| ≤ K * |b| := by
  rcases le_or_gt 0 b with hb | hb
  · rw [abs_of_nonneg hb]
    constructor
    · rintro (⟨-, h1, h2⟩ | ⟨hb0, h1, h2⟩)
      · exact abs_le.mpr ⟨neg_le.mp h2, h1⟩
      · have hb' : b = 0 := le_antisymm hb0 hb
        subst hb'
        simp only [mul_zero] at h1 h2 ⊢
        exact abs_le.mpr ⟨neg_le.mp h2, h1⟩
    · intro h
      obtain ⟨h1, h2⟩ := abs_le.mp h
      exact Or.inl ⟨hb, h2, neg_le.mpr h1⟩
  · rw [abs_of_neg hb, mul_neg, ← neg_mul]
    constructor
    · rintro (⟨hb0, -, -⟩ | ⟨-, h1, h2⟩)
      · exact absurd (lt_of_le_of_lt hb0 hb) (lt_irrefl 0)
      · exact abs_le.mpr ⟨neg_le.mp h2, h1⟩
    · intro h
      obtain ⟨h1, h2⟩ := abs_le.mp h
      exact Or.inr ⟨le_of_lt hb, h2, neg_le.mpr h1⟩

theorem definable_absLe {σ : Type*} (K : ℝ) (i j : σ) :
    (∅ : Set ℝ).Definable LRc {g : σ → ℝ | absLe K (g i) (g j)} := by
  have hA : (∅ : Set ℝ).Definable LRc
      {g : σ → ℝ | 0 ≤ g j ∧ g i ≤ K * g j ∧ -g i ≤ K * g j} := by
    have h := ((definable_const_le (0:ℝ) j).inter (definable_le_mul_const i j K)).inter
      (definable_neg_le_mul_const i j K)
    convert h using 1
    ext g; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
  have hB : (∅ : Set ℝ).Definable LRc
      {g : σ → ℝ | g j ≤ 0 ∧ g i ≤ -K * g j ∧ -g i ≤ -K * g j} := by
    have h := ((definable_le_const j 0).inter (definable_le_mul_const i j (-K))).inter
      (definable_neg_le_mul_const i j (-K))
    convert h using 1
    ext g; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
  have heq : {g : σ → ℝ | absLe K (g i) (g j)} =
      ({g : σ → ℝ | 0 ≤ g j ∧ g i ≤ K * g j ∧ -g i ≤ K * g j} ∪
        {g : σ → ℝ | g j ≤ 0 ∧ g i ≤ -K * g j ∧ -g i ≤ -K * g j}) := by
    ext g; simp only [Set.mem_ofPred_eq, Set.mem_union, absLe]
  rw [heq]; exact hA.union hB

/-! ## 3. Index types and coordinate maps -/

abbrev Idx (k : ℕ) := Fin (k + 3)
abbrev IdxU (k : ℕ) := Idx k ⊕ Fin 1
abbrev IdxUY (k : ℕ) := IdxU k ⊕ Fin 1

def wOf {k : ℕ} (g : IdxUY k → ℝ) : Fin (k + 3) → ℝ := fun i => g (Sum.inl (Sum.inl i))
def ctail {k : ℕ} (g : IdxUY k → ℝ) : Fin k → ℝ :=
  Fin.tail (Fin.tail (Fin.init (wOf g)))
def gtup {k : ℕ} (g : IdxUY k → ℝ) : Fin (k + 2) → ℝ :=
  Fin.cons (g (Sum.inl (Sum.inr 0))) (Fin.cons (g (Sum.inr 0)) (ctail g))

def gfun (k : ℕ) : Fin (k + 2) → IdxUY k :=
  Fin.cases (Sum.inl (Sum.inr (0 : Fin 1)))
    (Fin.cases (Sum.inr (0 : Fin 1))
      (fun j : Fin k => Sum.inl (Sum.inl (Fin.castSucc (Fin.succ (Fin.succ j))))))

theorem gtup_eq {k : ℕ} (g : IdxUY k → ℝ) : gtup g = g ∘ gfun k := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [gtup, ctail, gfun, Function.comp_apply]
      rfl

def graphSet {k : ℕ} (Y : Set (Fin (k+2) → ℝ)) : Set (IdxUY k → ℝ) := {g | gtup g ∈ Y}

theorem graphSet_definable {k : ℕ} {Y : Set (Fin (k+2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (graphSet Y) := by
  have h := hY.preimage_comp (gfun k)
  have hset : graphSet Y = (fun g : IdxUY k → ℝ => g ∘ gfun k) ⁻¹' Y := by
    ext g; simp only [graphSet, Set.mem_ofPred_eq, Set.mem_preimage]; rw [gtup_eq]
  rw [hset]; exact h

def goodBody {k : ℕ} (Y : Set (Fin (k+2) → ℝ)) (K₀ : ℝ) : Set (IdxUY k → ℝ) :=
  graphSet Y ∩ {g | absLe K₀ (g (Sum.inr 0)) (g (Sum.inl (Sum.inl (1 : Fin (k+3)))))}
    ∩ {g | absLe K₀ (g (Sum.inl (Sum.inl (1 : Fin (k+3))))) (g (Sum.inr 0))}

theorem goodBody_definable {k : ℕ} {Y : Set (Fin (k+2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) (K₀ : ℝ) :
    (∅ : Set ℝ).Definable LRc (goodBody Y K₀) := by
  have h1 : (∅ : Set ℝ).Definable LRc
      {g : IdxUY k → ℝ | absLe K₀ (g (Sum.inr 0)) (g (Sum.inl (Sum.inl (1 : Fin (k+3)))))} :=
    definable_absLe K₀ (Sum.inr (0:Fin 1)) (Sum.inl (Sum.inl (1 : Fin (k+3))))
  have h2 : (∅ : Set ℝ).Definable LRc
      {g : IdxUY k → ℝ | absLe K₀ (g (Sum.inl (Sum.inl (1 : Fin (k+3))))) (g (Sum.inr 0))} :=
    definable_absLe K₀ (Sum.inl (Sum.inl (1 : Fin (k+3)))) (Sum.inr (0:Fin 1))
  exact ((graphSet_definable hY).inter h1).inter h2

def univY {k : ℕ} (Y : Set (Fin (k+2) → ℝ)) (K₀ : ℝ) : Set (IdxU k → ℝ) :=
  {g | ∀ y : Fin 1 → ℝ, Sum.elim g y ∈ (goodBody Y K₀)ᶜ}

theorem univY_definable {k : ℕ} {Y : Set (Fin (k+2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) (K₀ : ℝ) :
    (∅ : Set ℝ).Definable LRc (univY Y K₀) :=
  ((goodBody_definable hY K₀).compl).forall_of_finite (α := IdxU k) (β := Fin 1)

def outer {k : ℕ} : Set (IdxU k → ℝ) :=
  {g | |g (Sum.inr 0) - g (Sum.inl 0)| < g (Sum.inl (Fin.last (k+2)))}

theorem outer_definable {k : ℕ} : (∅ : Set ℝ).Definable LRc (outer (k := k)) := by
  have h1 := definable_sub_lt (σ := IdxU k) (Sum.inr (0:Fin 1)) (Sum.inl (0 : Idx k))
    (Sum.inl (Fin.last (k+2)))
  have h2 := definable_sub_lt (σ := IdxU k) (Sum.inl (0 : Idx k)) (Sum.inr (0:Fin 1))
    (Sum.inl (Fin.last (k+2)))
  have heq : (outer (k := k)) =
      {g : IdxU k → ℝ | g (Sum.inr 0) - g (Sum.inl 0) < g (Sum.inl (Fin.last (k+2)))} ∩
      {g : IdxU k → ℝ | g (Sum.inl 0) - g (Sum.inr 0) < g (Sum.inl (Fin.last (k+2)))} := by
    ext g
    simp only [outer, Set.mem_ofPred_eq, Set.mem_inter_iff]
    rw [abs_lt]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, h1⟩
  rw [heq]; exact h1.inter h2

def notGood {k : ℕ} (Y : Set (Fin (k+2) → ℝ)) (K₀ : ℝ) : Set (Idx k → ℝ) :=
  {w | ∃ u : Fin 1 → ℝ, Sum.elim w u ∈ outer ∩ univY Y K₀}

theorem notGood_definable {k : ℕ} {Y : Set (Fin (k+2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) (K₀ : ℝ) :
    (∅ : Set ℝ).Definable LRc (notGood Y K₀) :=
  ((outer_definable (k := k)).inter (univY_definable hY K₀)).exists_of_finite
    (α := Idx k) (β := Fin 1)

/-! ## 4. Membership descriptions -/

lemma forall_fin_one_fun {P : ℝ → Prop} :
    (∀ t : Fin 1 → ℝ, P (t 0)) ↔ (∀ τ : ℝ, P τ) :=
  ⟨fun h τ => h (fun _ => τ), fun h t => h (t 0)⟩

lemma exists_fin_one_fun {P : ℝ → Prop} :
    (∃ t : Fin 1 → ℝ, P (t 0)) ↔ (∃ τ : ℝ, P τ) :=
  ⟨fun ⟨t, ht⟩ => ⟨t 0, ht⟩, fun ⟨τ, hτ⟩ => ⟨fun _ => τ, hτ⟩⟩

lemma wOf_sumElim {k : ℕ} (g : IdxU k → ℝ) (y : Fin 1 → ℝ) :
    wOf (Sum.elim g y) = fun i : Idx k => g (Sum.inl i) := rfl

lemma ctail_sumElim {k : ℕ} (g : IdxU k → ℝ) (y : Fin 1 → ℝ) :
    ctail (Sum.elim g y) = Fin.tail (Fin.tail (Fin.init (fun i : Idx k => g (Sum.inl i)))) := by
  rw [ctail, wOf_sumElim]

lemma gtup_sumElim {k : ℕ} (g : IdxU k → ℝ) (y : Fin 1 → ℝ) :
    gtup (Sum.elim g y) =
      (Fin.cons (g (Sum.inr 0))
        (Fin.cons (y 0) (Fin.tail (Fin.tail (Fin.init (fun i : Idx k => g (Sum.inl i))))))) := by
  simp only [gtup, ctail_sumElim, Sum.elim_inl, Sum.elim_inr]

lemma mem_goodBody {k : ℕ} {Y : Set (Fin (k+2) → ℝ)} {K₀ : ℝ} {g : IdxUY k → ℝ} :
    g ∈ goodBody Y K₀ ↔ gtup g ∈ Y ∧
        absLe K₀ (g (Sum.inr 0)) (g (Sum.inl (Sum.inl (1 : Fin (k+3))))) ∧
        absLe K₀ (g (Sum.inl (Sum.inl (1 : Fin (k+3))))) (g (Sum.inr 0)) := by
  simp only [goodBody, graphSet, Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

lemma mem_outer {k : ℕ} {g : IdxU k → ℝ} :
    g ∈ outer ↔ |g (Sum.inr 0) - g (Sum.inl 0)| < g (Sum.inl (Fin.last (k+2))) :=
  Iff.rfl

lemma mem_univY {k : ℕ} {Y : Set (Fin (k+2) → ℝ)} {K₀ : ℝ} {g : IdxU k → ℝ} :
    g ∈ univY Y K₀ ↔ ∀ y : ℝ, ¬ (Fin.cons (g (Sum.inr 0))
        (Fin.cons y (Fin.tail (Fin.tail (Fin.init (fun i : Idx k => g (Sum.inl i)))))) ∈ Y ∧
      |y| ≤ K₀ * |g (Sum.inl (1 : Fin (k+3)))| ∧
      |g (Sum.inl (1 : Fin (k+3)))| ≤ K₀ * |y|) := by
  rw [univY, Set.mem_ofPred_eq]
  constructor
  · intro h y
    have h' := h (fun _ => y)
    rw [Set.mem_compl_iff, mem_goodBody, gtup_sumElim, absLe_iff, absLe_iff] at h'
    simpa using h'
  · intro h yv
    rw [Set.mem_compl_iff, mem_goodBody, gtup_sumElim, absLe_iff, absLe_iff]
    exact h (yv 0)

lemma mem_notGood {k : ℕ} {Y : Set (Fin (k+2) → ℝ)} {K₀ : ℝ} {w : Idx k → ℝ} :
    w ∈ notGood Y K₀ ↔
      ∃ u : ℝ, |u - w 0| < w (Fin.last (k+2)) ∧
        ∀ y : ℝ, ¬ (Fin.cons u (Fin.cons y (Fin.tail (Fin.tail (Fin.init w)))) ∈ Y ∧
          |y| ≤ K₀ * |w 1| ∧ |w 1| ≤ K₀ * |y|) := by
  rw [notGood, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨u, huO, huU⟩
    refine ⟨u 0, ?_, ?_⟩
    · rw [mem_outer] at huO; simpa using huO
    · rw [mem_univY] at huU
      intro y; simpa using huU y
  · rintro ⟨u, huO, huU⟩
    refine ⟨fun _ => u, ?_, ?_⟩
    · rw [mem_outer]; simpa using huO
    · rw [mem_univY]; intro y; simpa using huU y

/-! ## 5. The set `S` -/

lemma not_isoGood_iff {k : ℕ} {Y : Set (Fin (k+2) → ℝ)} {K₀ : ℝ} {c : Fin k → ℝ}
    {x y₀ r : ℝ} :
    ¬ IsoGood Y K₀ c x y₀ r ↔ ∃ u : ℝ, |u - x| < r ∧
      ∀ y : ℝ, ¬ (Fin.cons u (Fin.cons y c) ∈ Y ∧ |y| ≤ K₀ * |y₀| ∧ |y₀| ≤ K₀ * |y|) := by
  simp only [IsoGood]
  push Not
  rfl

def Sset {k : ℕ} (Y : Set (Fin (k+2) → ℝ)) (K₀ : ℝ) : Set (Fin (k+3) → ℝ) :=
  {w | Fin.init w ∈ Y ∧ w 1 ≠ 0 ∧ 0 ≤ w (Fin.last (k+2)) ∧ w ∈ notGood Y K₀}

theorem definable_coord_ne_zero {σ : Type*} (i : σ) :
    (∅ : Set ℝ).Definable LRc {g : σ → ℝ | g i ≠ 0} := by
  refine definable_univ_iff_empty'.mp ?_
  have h := Work.WilC4.definable_ne_LRc (σ := σ) (MvPolynomial.X i) (0 : MvPolynomial σ ℝ)
  simpa using h

theorem Sset_definable {k : ℕ} {Y : Set (Fin (k+2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) (K₀ : ℝ) :
    (∅ : Set ℝ).Definable LRc (Sset Y K₀) := by
  have h1 : (∅ : Set ℝ).Definable LRc {w : Fin (k+3) → ℝ | Fin.init w ∈ Y} := by
    have h := hY.preimage_comp (Fin.castSucc : Fin (k+2) → Fin (k+3))
    have hset : {w : Fin (k+3) → ℝ | Fin.init w ∈ Y} =
        (fun g : Fin (k+3) → ℝ => g ∘ Fin.castSucc) ⁻¹' Y := by
      ext w; simp only [Set.mem_ofPred_eq, Set.mem_preimage]; rfl
    rw [hset]; exact h
  have h2 : (∅ : Set ℝ).Definable LRc {w : Fin (k+3) → ℝ | w 1 ≠ 0} :=
    definable_coord_ne_zero (1 : Fin (k+3))
  have h3 : (∅ : Set ℝ).Definable LRc {w : Fin (k+3) → ℝ | 0 ≤ w (Fin.last (k+2))} :=
    definable_const_le 0 (Fin.last (k+2))
  have h4 := notGood_definable hY K₀
  have h := ((h1.inter h2).inter h3).inter h4
  convert h using 1
  ext w; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Sset]; tauto

/-! ## 6. The `Fin` bookkeeping for `Fin.snoc` and `IsGLB` -/

lemma snoc_mem_Sset {k : ℕ} {Y : Set (Fin (k+2) → ℝ)} {K₀ : ℝ}
    {h : Fin (k+2) → ℝ} {t : ℝ} :
    (Fin.snoc h t : Fin (k+3) → ℝ) ∈ Sset Y K₀ ↔
      h ∈ Y ∧ h 1 ≠ 0 ∧ 0 ≤ t ∧
        ¬ IsoGood Y K₀ (Fin.tail (Fin.tail h)) (h 0) (h 1) t := by
  have h1 : Fin.init (Fin.snoc h t : Fin (k+3) → ℝ) = h :=
    Fin.init_snoc (α := fun _ => ℝ) (n := k+2) t h
  have h2 : (Fin.snoc h t : Fin (k+3) → ℝ) (1 : Fin (k+3)) = h 1 := by
    rw [show (1 : Fin (k+3)) = Fin.castSucc (1 : Fin (k+2)) from rfl,
      Fin.snoc_castSucc (α := fun _ => ℝ) (n := k+2)]
  have h3 : (Fin.snoc h t : Fin (k+3) → ℝ) (Fin.last (k+2)) = t :=
    Fin.snoc_last (α := fun _ => ℝ) (n := k+2) t h
  have h4 : (Fin.snoc h t : Fin (k+3) → ℝ) 0 = h 0 := by
    rw [show (0 : Fin (k+3)) = Fin.castSucc (0 : Fin (k+2)) from rfl,
      Fin.snoc_castSucc (α := fun _ => ℝ) (n := k+2)]
  rw [Sset, Set.mem_ofPred_eq, mem_notGood, h1, h2, h3, h4, not_isoGood_iff]

lemma not_isGLB_empty (ρ : ℝ) : ¬ IsGLB (∅ : Set ℝ) ρ := by
  intro h
  have hb : (ρ + 1) ∈ lowerBounds (∅ : Set ℝ) := by
    intro t ht; exact absurd ht (Set.notMem_empty t)
  have := h.2 hb
  linarith

lemma isGLB_and_const {A : Set ℝ} {P : Prop} {ρ : ℝ} :
    IsGLB {t : ℝ | P ∧ t ∈ A} ρ ↔ P ∧ IsGLB A ρ := by
  by_cases hP : P
  · have hset : {t : ℝ | P ∧ t ∈ A} = A := by ext t; simp [hP]
    rw [hset]; simp [hP]
  · have hset : {t : ℝ | P ∧ t ∈ A} = ∅ := by ext t; simp [hP]
    rw [hset]
    exact ⟨fun h => absurd h (not_isGLB_empty ρ), fun h => absurd h.1 hP⟩

lemma isGLB_Sset {k : ℕ} {Y : Set (Fin (k+2) → ℝ)} {K₀ : ℝ}
    {h : Fin (k+2) → ℝ} {ρ : ℝ} :
    IsGLB {t : ℝ | (Fin.snoc h t : Fin (k+3) → ℝ) ∈ Sset Y K₀} ρ ↔
      (h ∈ Y ∧ h 1 ≠ 0) ∧
        IsGLB {t : ℝ | 0 ≤ t ∧ ¬ IsoGood Y K₀ (Fin.tail (Fin.tail h)) (h 0) (h 1) t} ρ := by
  have hset : {t : ℝ | (Fin.snoc h t : Fin (k+3) → ℝ) ∈ Sset Y K₀} =
      {t : ℝ | (h ∈ Y ∧ h 1 ≠ 0) ∧
        t ∈ {t : ℝ | 0 ≤ t ∧ ¬ IsoGood Y K₀ (Fin.tail (Fin.tail h)) (h 0) (h 1) t}} := by
    ext t
    simp only [Set.mem_ofPred_eq]
    rw [snoc_mem_Sset]
    tauto
  rw [hset]
  exact isGLB_and_const

/-! ## 7. The index map `falong` and the lifted family `gv` -/

/-- The index map `Fin (k+2) → Fin (k+3)` skipping the `y₀`-slot `1`: it sends `0 ↦ 0`,
`1 ↦ k+2` (the value slot) and `j+2 ↦ j+2`.  In coordinates, the image under it of the graph
of `IsGLB` over `(x, y₀, c, r)` has coordinates `(x, ρ, c)`. -/
def falong (k : ℕ) : Fin (k+2) → Fin (k+3) :=
  Fin.cases (0 : Fin (k+3))
    (Fin.cases (Fin.last (k+2)) (fun j : Fin k => Fin.castSucc (Fin.succ (Fin.succ j))))

@[simp] lemma falong_zero (k : ℕ) : falong k (0 : Fin (k+2)) = (0 : Fin (k+3)) := rfl

@[simp] lemma falong_succ_zero (k : ℕ) :
    falong k (Fin.succ (0 : Fin (k+1))) = Fin.last (k+2) := rfl

@[simp] lemma falong_succ_succ (k : ℕ) (j : Fin k) :
    falong k (Fin.succ (Fin.succ j)) = Fin.castSucc (Fin.succ (Fin.succ j)) := rfl

/-- The tuple `(v 0, y₀, (Fin.tail (Fin.tail v)), v 1)` in `Fin (k+3)`: the unique point of
`ℝ^{k+3}` whose image under `falong` is `v` and whose second coordinate is `y₀`. -/
def gv {k : ℕ} (v : Fin (k+2) → ℝ) (y₀ : ℝ) : Fin (k+3) → ℝ :=
  Fin.snoc (Fin.cons (v 0) (Fin.cons y₀ (Fin.tail (Fin.tail v)) : Fin (k+1) → ℝ) :
    Fin (k+2) → ℝ) (v 1)

lemma gv_castSucc {k : ℕ} (v : Fin (k+2) → ℝ) (y₀ : ℝ) (m : Fin (k+2)) :
    gv v y₀ (Fin.castSucc m) =
      ((Fin.cons (v 0) (Fin.cons y₀ (Fin.tail (Fin.tail v)) : Fin (k+1) → ℝ) :
        Fin (k+2) → ℝ)) m :=
  Fin.snoc_castSucc (α := fun _ => ℝ) (n := k+2) (v 1) _ m

@[simp] lemma gv_zero {k : ℕ} (v : Fin (k+2) → ℝ) (y₀ : ℝ) :
    gv v y₀ (0 : Fin (k+3)) = v 0 := by
  rw [show (0 : Fin (k+3)) = Fin.castSucc (0 : Fin (k+2)) from rfl, gv_castSucc]
  exact Fin.cons_zero (α := fun _ => ℝ) (v 0) _

@[simp] lemma gv_one {k : ℕ} (v : Fin (k+2) → ℝ) (y₀ : ℝ) :
    gv v y₀ 1 = y₀ := by
  rw [show (1 : Fin (k+3)) = Fin.castSucc (1 : Fin (k+2)) from rfl, gv_castSucc,
    show (1 : Fin (k+2)) = Fin.succ (0 : Fin (k+1)) from rfl,
    Fin.cons_succ (α := fun _ => ℝ) (v 0)
      (Fin.cons y₀ (Fin.tail (Fin.tail v)) : Fin (k+1) → ℝ) 0]
  exact Fin.cons_zero (α := fun _ => ℝ) y₀ _

@[simp] lemma gv_succ_succ {k : ℕ} (v : Fin (k+2) → ℝ) (y₀ : ℝ) (j : Fin k) :
    gv v y₀ (Fin.castSucc (Fin.succ (Fin.succ j))) = v (Fin.succ (Fin.succ j)) := by
  rw [gv_castSucc,
    Fin.cons_succ (α := fun _ => ℝ) (v 0)
      (Fin.cons y₀ (Fin.tail (Fin.tail v)) : Fin (k+1) → ℝ),
    Fin.cons_succ (α := fun _ => ℝ) y₀ (Fin.tail (Fin.tail v))]
  rfl

@[simp] lemma gv_last {k : ℕ} (v : Fin (k+2) → ℝ) (y₀ : ℝ) :
    gv v y₀ (Fin.last (k+2)) = v 1 :=
  Fin.snoc_last (α := fun _ => ℝ) (n := k+2) (v 1) _

lemma gv_comp {k : ℕ} (v : Fin (k+2) → ℝ) (y₀ : ℝ) : gv v y₀ ∘ falong k = v := by
  funext i
  refine Fin.cases ?_ (fun i' => ?_) i
  · show gv v y₀ (falong k 0) = v 0
    rw [falong_zero]; exact gv_zero v y₀
  · refine Fin.cases ?_ (fun j => ?_) i'
    · show gv v y₀ (falong k (Fin.succ (0 : Fin (k+1)))) = v (Fin.succ (0 : Fin (k+1)))
      rw [falong_succ_zero, show v (Fin.succ (0 : Fin (k+1))) = v 1 from rfl]
      exact gv_last v y₀
    · show gv v y₀ (falong k (Fin.succ (Fin.succ j))) = v (Fin.succ (Fin.succ j))
      rw [falong_succ_succ]
      exact gv_succ_succ v y₀ j

lemma gv_init {k : ℕ} (v : Fin (k+2) → ℝ) (y₀ : ℝ) :
    Fin.init (gv v y₀) =
      ((Fin.cons (v 0) (Fin.cons y₀ (Fin.tail (Fin.tail v)) : Fin (k+1) → ℝ) :
        Fin (k+2) → ℝ)) :=
  Fin.init_snoc (α := fun _ => ℝ) (n := k+2) (v 1) _

lemma tail_tail_init_gv {k : ℕ} (v : Fin (k+2) → ℝ) (y₀ : ℝ) :
    Fin.tail (Fin.tail (Fin.init (gv v y₀))) = Fin.tail (Fin.tail v) := by
  rw [gv_init, Fin.tail_cons, Fin.tail_cons]

lemma head_init_gv {k : ℕ} (v : Fin (k+2) → ℝ) (y₀ : ℝ) :
    (Fin.init (gv v y₀)) 0 = v 0 := by
  rw [gv_init, Fin.cons_zero (α := fun _ => ℝ)]

lemma one_init_gv {k : ℕ} (v : Fin (k+2) → ℝ) (y₀ : ℝ) :
    (Fin.init (gv v y₀)) 1 = y₀ := by
  rw [gv_init, show (1 : Fin (k+2)) = Fin.succ (0 : Fin (k+1)) from rfl,
    Fin.cons_succ (α := fun _ => ℝ), Fin.cons_zero (α := fun _ => ℝ)]

lemma cons_cons_eq_one {k : ℕ} (a b : ℝ) (T : Fin k → ℝ) :
    ((Fin.cons a (Fin.cons b T) : Fin (k+2) → ℝ)) 1 = b := by
  rw [show (1 : Fin (k+2)) = Fin.succ (0 : Fin (k+1)) from rfl,
    Fin.cons_succ (α := fun _ => ℝ), Fin.cons_zero (α := fun _ => ℝ)]

/-- If `g ∘ falong = v` then the initial segment of `g` is `(v 0, g 1, Fin.tail (Fin.tail v))`. -/
lemma init_eq_of_comp {k : ℕ} {g : Fin (k+3) → ℝ} {v : Fin (k+2) → ℝ}
    (h : g ∘ falong k = v) :
    Fin.init g = ((Fin.cons (v 0) (Fin.cons (g 1) (Fin.tail (Fin.tail v)) : Fin (k+1) → ℝ) :
      Fin (k+2) → ℝ)) := by
  funext i
  refine Fin.cases ?_ (fun i' => ?_) i
  · show g (Fin.castSucc (0 : Fin (k+2))) = ((Fin.cons (v 0)
      (Fin.cons (g 1) (Fin.tail (Fin.tail v)) : Fin (k+1) → ℝ) : Fin (k+2) → ℝ)) 0
    rw [Fin.cons_zero (α := fun _ => ℝ)]
    have hh := congrFun h (0 : Fin (k+2))
    simp only [Function.comp_apply] at hh
    rw [falong_zero] at hh
    exact hh
  · refine Fin.cases ?_ (fun j => ?_) i'
    · show g (Fin.castSucc (Fin.succ (0 : Fin (k+1)))) = ((Fin.cons (v 0)
        (Fin.cons (g 1) (Fin.tail (Fin.tail v)) : Fin (k+1) → ℝ) : Fin (k+2) → ℝ))
          (Fin.succ (0 : Fin (k+1)))
      rw [Fin.cons_succ (α := fun _ => ℝ), Fin.cons_zero (α := fun _ => ℝ)]
      rfl
    · show g (Fin.castSucc (Fin.succ (Fin.succ j))) = ((Fin.cons (v 0)
        (Fin.cons (g 1) (Fin.tail (Fin.tail v)) : Fin (k+1) → ℝ) : Fin (k+2) → ℝ))
          (Fin.succ (Fin.succ j))
      rw [Fin.cons_succ (α := fun _ => ℝ), Fin.cons_succ (α := fun _ => ℝ)]
      have hh := congrFun h (Fin.succ (Fin.succ j))
      simp only [Function.comp_apply] at hh
      rw [falong_succ_succ] at hh
      exact hh

lemma tail_tail_init_eq_of_comp {k : ℕ} {g : Fin (k+3) → ℝ} {v : Fin (k+2) → ℝ}
    (h : g ∘ falong k = v) :
    Fin.tail (Fin.tail (Fin.init g)) = Fin.tail (Fin.tail v) := by
  rw [init_eq_of_comp h, Fin.tail_cons, Fin.tail_cons]

lemma init_head_eq_of_comp {k : ℕ} {g : Fin (k+3) → ℝ} {v : Fin (k+2) → ℝ}
    (h : g ∘ falong k = v) : (Fin.init g) 0 = v 0 := by
  rw [init_eq_of_comp h, Fin.cons_zero (α := fun _ => ℝ)]

lemma init_one_eq_of_comp {k : ℕ} {g : Fin (k+3) → ℝ} {v : Fin (k+2) → ℝ}
    (h : g ∘ falong k = v) : (Fin.init g) 1 = g 1 := by
  rw [init_eq_of_comp h, cons_cons_eq_one]

lemma last_eq_of_comp {k : ℕ} {g : Fin (k+3) → ℝ} {v : Fin (k+2) → ℝ}
    (h : g ∘ falong k = v) : g (Fin.last (k+2)) = v 1 := by
  have hh := congrFun h (Fin.succ (0 : Fin (k+1)))
  simp only [Function.comp_apply] at hh
  rw [falong_succ_zero] at hh
  exact hh

/-! ## 8. Definability of `RhoFam` -/

theorem rhoFam_aux {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) (K₀ : ℝ) :
    (∅ : Set ℝ).Definable LRc (RhoFam Y K₀) := by
  have hS : (∅ : Set ℝ).Definable LRc (Sset Y K₀) := Sset_definable hY K₀
  have hGLB : (∅ : Set ℝ).Definable LRc
      {u : Fin (k+3) → ℝ |
        IsGLB {t : ℝ | (Fin.snoc (Fin.init u) t : Fin (k+3) → ℝ) ∈ Sset Y K₀}
          (u (Fin.last (k+2)))} :=
    Work.WilC4.definable_isGLB_family (n := k+2) hS
  have hW : (∅ : Set ℝ).Definable LRc
      ((fun g : Fin (k+3) → ℝ => g ∘ falong k) ''
        {u : Fin (k+3) → ℝ |
          IsGLB {t : ℝ | (Fin.snoc (Fin.init u) t : Fin (k+3) → ℝ) ∈ Sset Y K₀}
            (u (Fin.last (k+2)))}) :=
    hGLB.image_comp (falong k)
  have hset : RhoFam Y K₀ =
      (fun g : Fin (k+3) → ℝ => g ∘ falong k) ''
        {u : Fin (k+3) → ℝ |
          IsGLB {t : ℝ | (Fin.snoc (Fin.init u) t : Fin (k+3) → ℝ) ∈ Sset Y K₀}
            (u (Fin.last (k+2)))} := by
    ext v
    simp only [Set.mem_image, Set.mem_ofPred_eq, RhoFam]
    constructor
    · rintro ⟨y₀, hy, hy0, hglb⟩
      refine ⟨gv v y₀, ?_, gv_comp v y₀⟩
      rw [isGLB_Sset]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [gv_init]; exact hy
      · rw [one_init_gv]; exact hy0
      · rw [tail_tail_init_gv, head_init_gv, one_init_gv, gv_last]; exact hglb
    · rintro ⟨g, hg, hgv⟩
      obtain ⟨⟨hinY, hne⟩, hglb2⟩ :=
        (isGLB_Sset (h := Fin.init g) (ρ := g (Fin.last (k+2)))).mp hg
      refine ⟨g 1, ?_, ?_, ?_⟩
      · rwa [init_eq_of_comp hgv] at hinY
      · rwa [init_one_eq_of_comp hgv] at hne
      · rw [tail_tail_init_eq_of_comp hgv, init_head_eq_of_comp hgv,
          init_one_eq_of_comp hgv, last_eq_of_comp hgv] at hglb2
        exact hglb2
  rw [hset]
  exact hW

end Work.WilVP.RhoAux

namespace Work.WilVP

open RhoAux

/-- `Work.WilVP.RhoFam Y K₀ ⊆ ℝ^{k+2}` (coordinates `(x, ρ, c)`) is `∅`-definable in `LRc`. -/
theorem rhoFam_definable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) (K₀ : ℝ) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilVP.RhoFam Y K₀) :=
  RhoAux.rhoFam_aux hY K₀

end Work.WilVP
