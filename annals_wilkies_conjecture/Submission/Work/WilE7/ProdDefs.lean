/-
  Area E7: the *product* of two restricted semi-Pfaffian sets.

  `WilkiesDesign.E.SemiPf k` is a restricted semi-Pfaffian set in `ℝ^k`, given as a DNF over a
  single exp-affine (EA) chain (`SemiPf.r` exponential functions).  The target lemma
  `Work.WilE7.prod_semiPf` asks that the product

      { z : ℝ^{k+k'} | projFirst k k' z ∈ X.set ∧ projSnd k k' z ∈ X'.set }

  of two such sets is again semi-Pfaffian, of format bounded by a constant depending only on the
  two formats and degree bounded by a polynomial in the two degrees.

  The construction is the obvious one: the ambient space is `ℝ^{k+k'}`, the chain of the product
  is the concatenation of the two chains (`EAChain.prod`, with the extra `k'` coordinates of the
  first chain set to zero and the first `k` coordinates of the second chain set to zero), and the
  DNF is the product of the two DNF lists, each pair `(B, B')` being combined into a single basic
  set `Basic.prod B B'` whose equations/inequalities are the two lists merged after reindexing
  the variables (`EAPoly.prodL` / `EAPoly.prodR`).

  Two technical points are handled here:

  * `redBasics X` replaces `X.basics` by `[trivialB]` as soon as `X` contains a *trivial* basic
    (empty `eqs` and `pos`).  Such a basic imposes no condition, so it makes `X.set` the whole
    cube; the replacement keeps the point set but makes the number of basics bounded by `max 1 X.deg`,
    which is what makes the degree of the product polynomial in the two degrees (a list of `m`
    trivial basics has degree `0` but length `m`).

  * the degree of `Basic.prod B B'` is `≤ B.deg + B'.deg`, because `EAPoly.prodL`/`prodR` are
    polynomial *renamings* and `MvPolynomial.rename` never raises the total degree.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## Reindexing a sum of a list -/

/-- Monotonicity of `List.sum` under a pointwise bound of the summands. -/
theorem sum_map_le_of_pointwise {α : Type*} (l : List α) (f g : α → ℕ)
    (h : ∀ a ∈ l, f a ≤ g a) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

/-! ## The variable reindexings `prodL` / `prodR`

Variable `Sum.inl i : Fin k ⊕ Fin r` is the coordinate `x i` and `Sum.inr j : Fin r` is the
exponential `exp (ℓ_j x)`. -/

/-- The variable map embedding the `k + r` variables of the first factor into the product. -/
def prodLMap {k k' r r' : ℕ} : Fin k ⊕ Fin r → Fin (k + k') ⊕ Fin (r + r')
  | Sum.inl i => Sum.inl (Fin.castAdd k' i)
  | Sum.inr j => Sum.inr (Fin.castAdd r' j)

/-- The variable map embedding the `k' + r'` variables of the second factor into the product. -/
def prodRMap {k k' r r' : ℕ} : Fin k' ⊕ Fin r' → Fin (k + k') ⊕ Fin (r + r')
  | Sum.inl i => Sum.inl (Fin.natAdd k i)
  | Sum.inr j => Sum.inr (Fin.natAdd r j)

/-- Reindex a polynomial of the first factor as a polynomial of the product chain. -/
def EAPoly.prodL {k k' r r' : ℕ} (Q : EAPoly k r) : EAPoly (k + k') (r + r') :=
  MvPolynomial.rename (prodLMap (k := k) (k' := k') (r := r) (r' := r')) Q

/-- Reindex a polynomial of the second factor as a polynomial of the product chain. -/
def EAPoly.prodR {k k' r r' : ℕ} (Q : EAPoly k' r') : EAPoly (k + k') (r + r') :=
  MvPolynomial.rename (prodRMap (k := k) (k' := k') (r := r) (r' := r')) Q

/-! ## The product chain -/

/-- The concatenated chain: its `j`-th function is the `j`-th function of `c` (for `j < r`) or of
`c'` (for `j ≥ r`), the coordinates of the *other* factor being given coefficient `0`. -/
def EAChain.prod {k k' r r' : ℕ} (c : EAChain k r) (c' : EAChain k' r') :
    EAChain (k + k') (r + r') where
  a := fun j i => Fin.addCases
    (fun (j₁ : Fin r) => Fin.addCases (fun (i₁ : Fin k) => c.a j₁ i₁) (fun (_ : Fin k') => 0) i)
    (fun (j₂ : Fin r') => Fin.addCases (fun (_ : Fin k) => 0) (fun (i₂ : Fin k') => c'.a j₂ i₂) i)
    j
  b := fun j => Fin.addCases (fun (j₁ : Fin r) => c.b j₁) (fun (j₂ : Fin r') => c'.b j₂) j

theorem EAChain.prod_a_left {k k' r r' : ℕ} (c : EAChain k r) (c' : EAChain k' r')
    (j : Fin r) (i : Fin (k + k')) :
    (EAChain.prod c c').a (Fin.castAdd r' j) i
      = Fin.addCases (fun (i₁ : Fin k) => c.a j i₁) (fun (_ : Fin k') => 0) i := by
  simp only [EAChain.prod, Fin.addCases_left]

theorem EAChain.prod_a_right {k k' r r' : ℕ} (c : EAChain k r) (c' : EAChain k' r')
    (j : Fin r') (i : Fin (k + k')) :
    (EAChain.prod c c').a (Fin.natAdd r j) i
      = Fin.addCases (fun (_ : Fin k) => 0) (fun (i₂ : Fin k') => c'.a j i₂) i := by
  simp only [EAChain.prod, Fin.addCases_right]

theorem EAChain.prod_b_left {k k' r r' : ℕ} (c : EAChain k r) (c' : EAChain k' r') (j : Fin r) :
    (EAChain.prod c c').b (Fin.castAdd r' j) = c.b j := by
  simp only [EAChain.prod, Fin.addCases_left]

theorem EAChain.prod_b_right {k k' r r' : ℕ} (c : EAChain k r) (c' : EAChain k' r') (j : Fin r') :
    (EAChain.prod c c').b (Fin.natAdd r j) = c'.b j := by
  simp only [EAChain.prod, Fin.addCases_right]

/-- The chain functions of the first factor, read in the product chain. -/
theorem EAChain.prod_ell_left {k k' r r' : ℕ} (c : EAChain k r) (c' : EAChain k' r')
    (j : Fin r) (z : Fin (k + k') → ℝ) :
    (EAChain.prod c c').ell (Fin.castAdd r' j) z = c.ell j (projFirst k k' z) := by
  rw [EAChain.ell, EAChain.ell, prod_b_left, Fin.sum_univ_add]
  have hzero : (∑ i : Fin k', (EAChain.prod c c').a (Fin.castAdd r' j) (Fin.natAdd k i)
      * z (Fin.natAdd k i)) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    rw [prod_a_left]; simp only [Fin.addCases_right]; ring
  rw [hzero, add_zero]
  congr 1
  apply Finset.sum_congr rfl; intro i _
  rw [prod_a_left]; simp only [Fin.addCases_left, projFirst]

/-- The chain functions of the second factor, read in the product chain. -/
theorem EAChain.prod_ell_right {k k' r r' : ℕ} (c : EAChain k r) (c' : EAChain k' r')
    (j : Fin r') (z : Fin (k + k') → ℝ) :
    (EAChain.prod c c').ell (Fin.natAdd r j) z = c'.ell j (projSnd k k' z) := by
  rw [EAChain.ell, EAChain.ell, prod_b_right, Fin.sum_univ_add]
  have hzero : (∑ i : Fin k, (EAChain.prod c c').a (Fin.natAdd r j) (Fin.castAdd k' i)
      * z (Fin.castAdd k' i)) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    rw [prod_a_right]; simp only [Fin.addCases_left]; ring
  rw [hzero, zero_add]
  congr 1
  apply Finset.sum_congr rfl; intro i _
  rw [prod_a_right]; simp only [Fin.addCases_right, projSnd]

/-- Evaluation of a reindexed polynomial of the first factor in the product chain. -/
theorem EAPoly.eaEval_prodL {k k' r r' : ℕ} (c : EAChain k r) (c' : EAChain k' r')
    (Q : EAPoly k r) (z : Fin (k + k') → ℝ) :
    eaEval (EAChain.prod c c') (EAPoly.prodL Q) z = eaEval c Q (projFirst k k' z) := by
  rw [eaEval, EAPoly.prodL, MvPolynomial.eval_rename, eaEval]
  have hfun : (Sum.elim z fun j => Real.exp ((EAChain.prod c c').ell j z)) ∘
        (prodLMap (k := k) (k' := k') (r := r) (r' := r')) =
      Sum.elim (projFirst k k' z) fun j => Real.exp (c.ell j (projFirst k k' z)) := by
    funext s
    rcases s with i | j
    · rfl
    · simp only [Function.comp_apply, Sum.elim_inr]
      exact congrArg Real.exp (EAChain.prod_ell_left c c' j z)
  rw [hfun]

/-- Evaluation of a reindexed polynomial of the second factor in the product chain. -/
theorem EAPoly.eaEval_prodR {k k' r r' : ℕ} (c : EAChain k r) (c' : EAChain k' r')
    (Q : EAPoly k' r') (z : Fin (k + k') → ℝ) :
    eaEval (EAChain.prod c c') (EAPoly.prodR Q) z = eaEval c' Q (projSnd k k' z) := by
  rw [eaEval, EAPoly.prodR, MvPolynomial.eval_rename, eaEval]
  have hfun : (Sum.elim z fun j => Real.exp ((EAChain.prod c c').ell j z)) ∘
        (prodRMap (k := k) (k' := k') (r := r) (r' := r')) =
      Sum.elim (projSnd k k' z) fun j => Real.exp (c'.ell j (projSnd k k' z)) := by
    funext s
    rcases s with i | j
    · rfl
    · simp only [Function.comp_apply, Sum.elim_inr]
      exact congrArg Real.exp (EAChain.prod_ell_right c c' j z)
  rw [hfun]

/-! ## `Basic.prod`: merging two basic sets -/

theorem atomDeg_prodL_le {k k' r r' : ℕ} (Q : EAPoly k r) :
    atomDeg (EAPoly.prodL (k' := k') (r' := r') Q) ≤ atomDeg Q := by
  simp only [atomDeg, EAPoly.prodL]
  exact Nat.add_le_add_right (MvPolynomial.totalDegree_rename_le _ Q) 1

theorem atomDeg_prodR_le {k k' r r' : ℕ} (Q : EAPoly k' r') :
    atomDeg (EAPoly.prodR (k := k) (r := r) Q) ≤ atomDeg Q := by
  simp only [atomDeg, EAPoly.prodR]
  exact Nat.add_le_add_right (MvPolynomial.totalDegree_rename_le _ Q) 1

/-- Merge two basic sets over the two factors into one basic set over the product chain. -/
def Basic.prod {k k' r r' : ℕ} (B : Basic k r) (B' : Basic k' r') :
    Basic (k + k') (r + r') :=
  ⟨B.eqs.map (EAPoly.prodL (k' := k') (r' := r')) ++ B'.eqs.map (EAPoly.prodR (k := k) (r := r)),
   B.pos.map (EAPoly.prodL (k' := k') (r' := r')) ++ B'.pos.map (EAPoly.prodR (k := k) (r := r))⟩

/-- `Basic.prod B B'` holds at `z` exactly when `B` holds at `projFirst z` and `B'` at `projSnd z`. -/
theorem Basic.holds_prod {k k' r r' : ℕ} (c : EAChain k r) (c' : EAChain k' r')
    (B : Basic k r) (B' : Basic k' r') (z : Fin (k + k') → ℝ) :
    (Basic.prod B B').holds (EAChain.prod c c') z ↔
      B.holds c (projFirst k k' z) ∧ B'.holds c' (projSnd k k' z) := by
  simp only [Basic.holds, Basic.prod]
  constructor
  · rintro ⟨he, hp⟩
    refine ⟨⟨fun f hf => ?_, fun g hg => ?_⟩, ⟨fun f hf => ?_, fun g hg => ?_⟩⟩
    · have h' := he (EAPoly.prodL (k' := k') (r' := r') f)
        (List.mem_append_left _ (List.mem_map_of_mem hf))
      rwa [EAPoly.eaEval_prodL] at h'
    · have h' := hp (EAPoly.prodL (k' := k') (r' := r') g)
        (List.mem_append_left _ (List.mem_map_of_mem hg))
      rwa [EAPoly.eaEval_prodL] at h'
    · have h' := he (EAPoly.prodR (k := k) (r := r) f)
        (List.mem_append_right _ (List.mem_map_of_mem hf))
      rwa [EAPoly.eaEval_prodR] at h'
    · have h' := hp (EAPoly.prodR (k := k) (r := r) g)
        (List.mem_append_right _ (List.mem_map_of_mem hg))
      rwa [EAPoly.eaEval_prodR] at h'
  · rintro ⟨⟨he₁, hp₁⟩, ⟨he₂, hp₂⟩⟩
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · rcases List.mem_append.mp hf with hf | hf
      · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
        rw [EAPoly.eaEval_prodL]; exact he₁ f₀ hf₀
      · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
        rw [EAPoly.eaEval_prodR]; exact he₂ f₀ hf₀
    · rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
        rw [EAPoly.eaEval_prodL]; exact hp₁ g₀ hg₀
      · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
        rw [EAPoly.eaEval_prodR]; exact hp₂ g₀ hg₀

/-- Merging does not raise the degree. -/
theorem Basic.prod_deg_le {k k' r r' : ℕ} (B : Basic k r) (B' : Basic k' r') :
    (Basic.prod B B').deg ≤ B.deg + B'.deg := by
  have h1 : ((B.eqs.map (EAPoly.prodL (k' := k') (r' := r'))).map atomDeg).sum
      ≤ (B.eqs.map atomDeg).sum := by
    rw [List.map_map]
    exact sum_map_le_of_pointwise B.eqs _ _ (fun Q _ => atomDeg_prodL_le Q)
  have h2 : ((B.pos.map (EAPoly.prodL (k' := k') (r' := r'))).map atomDeg).sum
      ≤ (B.pos.map atomDeg).sum := by
    rw [List.map_map]
    exact sum_map_le_of_pointwise B.pos _ _ (fun Q _ => atomDeg_prodL_le Q)
  have h3 : ((B'.eqs.map (EAPoly.prodR (k := k) (r := r))).map atomDeg).sum
      ≤ (B'.eqs.map atomDeg).sum := by
    rw [List.map_map]
    exact sum_map_le_of_pointwise B'.eqs _ _ (fun Q _ => atomDeg_prodR_le Q)
  have h4 : ((B'.pos.map (EAPoly.prodR (k := k) (r := r))).map atomDeg).sum
      ≤ (B'.pos.map atomDeg).sum := by
    rw [List.map_map]
    exact sum_map_le_of_pointwise B'.pos _ _ (fun Q _ => atomDeg_prodR_le Q)
  simp only [Basic.deg, Basic.prod, List.map_append, List.sum_append]
  linarith

/-! ## `redBasics`: discarding the multiplicity of trivial basic sets -/

/-- The basic set with no conditions at all; it holds everywhere on the cube. -/
def trivialB (k r : ℕ) : Basic k r := ⟨[], []⟩

theorem Basic.holds_of_nil {k r : ℕ} (c : EAChain k r) {B : Basic k r} (x : Fin k → ℝ)
    (he : B.eqs = []) (hp : B.pos = []) : B.holds c x := by
  refine ⟨fun f hf => ?_, fun g hg => ?_⟩
  · rw [he] at hf; exact absurd hf List.not_mem_nil
  · rw [hp] at hg; exact absurd hg List.not_mem_nil

theorem trivialB_holds {k r : ℕ} (c : EAChain k r) (x : Fin k → ℝ) : (trivialB k r).holds c x :=
  Basic.holds_of_nil c x rfl rfl

/-- `X` contains a basic set imposing no condition.  Then `X.set` is the whole cube. -/
def hasTrivial {k : ℕ} (X : SemiPf k) : Prop := ∃ B ∈ X.basics, B.eqs = [] ∧ B.pos = []

/-- The DNF list of `X`, with a trivial branch collapsed to a single trivial branch. -/
noncomputable def redBasics {k : ℕ} (X : SemiPf k) : List (Basic k X.r) :=
  if hasTrivial X then [trivialB k X.r] else X.basics

/-- `redBasics` does not change which points are covered. -/
theorem exists_holds_redBasics {k : ℕ} (X : SemiPf k) (y : Fin k → ℝ) :
    (∃ B ∈ redBasics X, B.holds X.c y) ↔ ∃ B ∈ X.basics, B.holds X.c y := by
  by_cases h : hasTrivial X
  · rw [show redBasics X = [trivialB k X.r] from if_pos h]
    constructor
    · intro _; obtain ⟨B, hB, he, hp⟩ := h
      exact ⟨B, hB, Basic.holds_of_nil X.c y he hp⟩
    · intro _; exact ⟨trivialB k X.r, List.mem_singleton.mpr rfl, trivialB_holds X.c y⟩
  · rw [show redBasics X = X.basics from if_neg h]

/-- Length of a list bounded below by `1` on every entry is bounded by its sum. -/
theorem length_le_sum_map {α : Type*} (l : List α) (f : α → ℕ) (hf : ∀ a ∈ l, 1 ≤ f a) :
    l.length ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have ha : 1 ≤ f a := hf a List.mem_cons_self
    have ht := ih (fun b hb => hf b (List.mem_cons_of_mem a hb))
    omega

theorem one_le_basic_deg {k r : ℕ} (B : Basic k r) (h : B.eqs ++ B.pos ≠ []) : 1 ≤ B.deg := by
  have h1 : (B.eqs ++ B.pos).length ≤ B.deg := by
    rw [Basic.deg]
    exact length_le_sum_map _ atomDeg (fun a _ => Nat.le_add_left 1 a.totalDegree)
  have h2 : 1 ≤ (B.eqs ++ B.pos).length := by
    cases hl : B.eqs ++ B.pos with
    | nil => exact absurd hl h
    | cons a t => simp
  omega

/-- The number of branches of `redBasics X` is bounded by `max 1 X.deg`. -/
theorem redBasics_length_le {k : ℕ} (X : SemiPf k) : (redBasics X).length ≤ max 1 X.deg := by
  by_cases h : hasTrivial X
  · rw [show redBasics X = [trivialB k X.r] from if_pos h]; simp
  · rw [show redBasics X = X.basics from if_neg h]
    have hle : X.basics.length ≤ X.deg := by
      rw [SemiPf.deg]
      apply length_le_sum_map
      intro B hB
      apply one_le_basic_deg
      intro hnil
      rw [List.append_eq_nil_iff] at hnil
      exact h ⟨B, hB, hnil.1, hnil.2⟩
    exact le_trans hle (le_max_right _ _)

/-- The total degree of `redBasics X` is bounded by `X.deg`. -/
theorem redBasics_deg_le {k : ℕ} (X : SemiPf k) : ((redBasics X).map Basic.deg).sum ≤ X.deg := by
  by_cases h : hasTrivial X
  · rw [show redBasics X = [trivialB k X.r] from if_pos h]
    simp [trivialB, Basic.deg]
  · rw [show redBasics X = X.basics from if_neg h]
    exact le_rfl

/-! ## The product of two semi-Pfaffian sets -/

/-- The product of two restricted semi-Pfaffian sets. -/
noncomputable def SemiPf.prod {k k' : ℕ} (X : SemiPf k) (X' : SemiPf k') : SemiPf (k + k') where
  r := X.r + X'.r
  c := EAChain.prod X.c X'.c
  basics := ((redBasics X).product (redBasics X')).map (fun p => Basic.prod p.1 p.2)

@[simp] theorem SemiPf.prod_r {k k' : ℕ} (X : SemiPf k) (X' : SemiPf k') :
    (SemiPf.prod X X').r = X.r + X'.r := rfl

@[simp] theorem SemiPf.prod_c {k k' : ℕ} (X : SemiPf k) (X' : SemiPf k') :
    (SemiPf.prod X X').c = EAChain.prod X.c X'.c := rfl

@[simp] theorem SemiPf.prod_basics {k k' : ℕ} (X : SemiPf k) (X' : SemiPf k') :
    (SemiPf.prod X X').basics
      = ((redBasics X).product (redBasics X')).map (fun p => Basic.prod p.1 p.2) := rfl

/-! ## The arithmetic of the degree bound -/

/-- Arithmetic core of the degree bound for the product. -/
theorem deg_bound_arith (d d' n n' S S' : ℕ) (hn : n ≤ max 1 d) (hn' : n' ≤ max 1 d')
    (hS : S ≤ d) (hS' : S' ≤ d') :
    n' * S + n * S' ≤ 2 * (1 + (d + d')) ^ 2 := by
  have hn1 : n' ≤ 1 + d' := le_trans hn' (by omega)
  have hS1 : S ≤ 1 + d := le_trans hS (by omega)
  have h1 : n' * S ≤ (1 + d') * (1 + d) := Nat.mul_le_mul hn1 hS1
  have hn2 : n ≤ 1 + d := le_trans hn (by omega)
  have hS2 : S' ≤ 1 + d' := le_trans hS' (by omega)
  have h2 : n * S' ≤ (1 + d) * (1 + d') := Nat.mul_le_mul hn2 hS2
  have h3 : (1 + d') * (1 + d) + (1 + d) * (1 + d') = 2 * ((1 + d) * (1 + d')) := by ring
  have h4 : (1 + d) * (1 + d') ≤ (1 + d + d') ^ 2 := by
    have hlt : 1 + d' ≤ 1 + d + d' := by omega
    calc (1 + d) * (1 + d') ≤ (1 + d) * (1 + d + d') := Nat.mul_le_mul_left (1 + d) hlt
      _ ≤ (1 + d + d') * (1 + d + d') :=
          Nat.mul_le_mul_right (1 + d + d') (Nat.le_add_right (1 + d) d')
      _ = (1 + d + d') ^ 2 := by ring
  calc n' * S + n * S' ≤ (1 + d') * (1 + d) + (1 + d) * (1 + d') := add_le_add h1 h2
    _ = 2 * ((1 + d) * (1 + d')) := h3
    _ ≤ 2 * (1 + d + d') ^ 2 := Nat.mul_le_mul_left 2 h4
    _ = 2 * (1 + (d + d')) ^ 2 := by rw [Nat.add_assoc]

end Work.WilE7
