import Mathlib.Algebra.Lie.UniversalEnveloping

noncomputable section
universe u

namespace Commons.Algebra.Lie.PBW

attribute [local instance 100] LieRing.ofAssociativeRing

section PBWSpanning
variable {K L ι : Type u} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [LinearOrder ι]

/-- The word map: product in `U` of the `ι`-images of `e i` for `i : ι` in `w`. -/
def pbwspan_stWord (e : Module.Basis ι K L) (w : List ι) : UniversalEnvelopingAlgebra K L :=
  (w.map (fun i => UniversalEnvelopingAlgebra.ι K (e i))).prod

@[simp] lemma pbwspan_stWord_nil (e : Module.Basis ι K L) :
    pbwspan_stWord e [] = 1 := by
  simp [pbwspan_stWord]

@[simp] lemma pbwspan_stWord_cons (e : Module.Basis ι K L) (a : ι) (w : List ι) :
    pbwspan_stWord e (a :: w) = UniversalEnvelopingAlgebra.ι K (e a) * pbwspan_stWord e w := by
  simp [pbwspan_stWord]

@[simp] lemma pbwspan_stWord_cons2 (e : Module.Basis ι K L) (a b : ι) (w : List ι) :
    pbwspan_stWord e (a :: b :: w) =
      UniversalEnvelopingAlgebra.ι K (e a) * UniversalEnvelopingAlgebra.ι K (e b) *
        pbwspan_stWord e w := by
  simp [pbwspan_stWord, ← mul_assoc]

lemma pbwspan_stWord_append (e : Module.Basis ι K L) (u v : List ι) :
    pbwspan_stWord e (u ++ v) = pbwspan_stWord e u * pbwspan_stWord e v := by
  simp [pbwspan_stWord]

/-- The commutation relation `ι(e a) * ι(e b) = ι(e b) * ι(e a) + ι ⁅e a, e b⁆` in `U`. -/
lemma pbwspan_iota_swap (e : Module.Basis ι K L) (a b : ι) :
    UniversalEnvelopingAlgebra.ι K (e a) * UniversalEnvelopingAlgebra.ι K (e b) =
      UniversalEnvelopingAlgebra.ι K (e b) * UniversalEnvelopingAlgebra.ι K (e a)
        + UniversalEnvelopingAlgebra.ι K ⁅e a, e b⁆ := by
  have h := LieHom.map_lie (UniversalEnvelopingAlgebra.ι K) (e a) (e b)
  rw [LieRing.of_associative_ring_bracket] at h
  rw [h]
  abel

/-- The universal enveloping algebra is generated, as an algebra, by the image of `ι`. -/
lemma pbwspan_uea_adjoin_range_ι (K L : Type u) [Field K] [LieRing L] [LieAlgebra K L] :
    Algebra.adjoin K (Set.range (fun x : L => UniversalEnvelopingAlgebra.ι K x)) = ⊤ := by
  let φ : TensorAlgebra K L →ₐ[K] UniversalEnvelopingAlgebra K L :=
    UniversalEnvelopingAlgebra.mkAlgHom K L
  have hsurj : Function.Surjective φ := by
    change Function.Surjective (RingCon.mkₐ K (UniversalEnvelopingAlgebra.ringCon K L))
    exact RingCon.mkₐ_surjective (UniversalEnvelopingAlgebra.ringCon K L)
  have himg : φ '' Set.range (fun x : L => TensorAlgebra.ι K x) =
      Set.range (fun x : L => UniversalEnvelopingAlgebra.ι K x) := by
    rw [← Set.range_comp]
    apply congrArg Set.range
    funext x
    exact (UniversalEnvelopingAlgebra.ι_apply K x).symm
  rw [← himg]
  rw [← AlgHom.map_adjoin]
  rw [TensorAlgebra.adjoin_range_ι (M := L)]
  have hmap : Subalgebra.map φ (⊤ : Subalgebra K (TensorAlgebra K L)) = φ.range := by
    ext x
    simp [AlgHom.mem_range]
  rw [hmap]
  apply le_antisymm
  · intro x hx
    trivial
  · intro x hx
    rw [AlgHom.mem_range]
    exact hsurj x

/-- The set of standard monomials (products over nondecreasing words). -/
def pbwspan_stdSet (e : Module.Basis ι K L) : Set (UniversalEnvelopingAlgebra K L) :=
  {x | ∃ w : {w : List ι // w.Pairwise (fun a b : ι => a ≤ b)},
    x = pbwspan_stWord e w.1}

/-- The submodule spanned by the standard monomials. -/
def pbwspan_spanStd (e : Module.Basis ι K L) : Submodule K (UniversalEnvelopingAlgebra K L) :=
  Submodule.span K (pbwspan_stdSet e)

/-- The set of all word products (words need not be sorted). -/
def pbwspan_allSet (e : Module.Basis ι K L) : Set (UniversalEnvelopingAlgebra K L) :=
  {x | ∃ w : List ι, x = pbwspan_stWord e w}

/-- The submodule spanned by all word products. -/
def pbwspan_spanAll (e : Module.Basis ι K L) : Submodule K (UniversalEnvelopingAlgebra K L) :=
  Submodule.span K (pbwspan_allSet e)

lemma pbwspan_spanAll_one_mem (e : Module.Basis ι K L) : (1 : UniversalEnvelopingAlgebra K L) ∈ pbwspan_spanAll e := by
  apply Submodule.subset_span
  exact ⟨[], by simp [pbwspan_allSet, pbwspan_stWord]⟩

/-- Every `ι`-image of a basis element is an (all-)word product, hence lies in `pbwspan_spanAll`. -/
lemma pbwspan_spanAll_basis_mem (e : Module.Basis ι K L) (i : ι) :
    UniversalEnvelopingAlgebra.ι K (e i) ∈ pbwspan_spanAll e := by
  apply Submodule.subset_span
  exact ⟨[i], by simp [pbwspan_allSet, pbwspan_stWord]⟩

/-- `ι` maps `L` into any `K`-submodule of `U` that contains all the `ι (e i)`. -/
lemma pbwspan_iota_mem (e : Module.Basis ι K L) (x : L)
    (S : Submodule K (UniversalEnvelopingAlgebra K L))
    (hgen : ∀ i : ι, UniversalEnvelopingAlgebra.ι K (e i) ∈ S) :
    UniversalEnvelopingAlgebra.ι K x ∈ S := by
  have hx : x = (e.repr x).sum (fun i ci => ci • e i) := by
    rw [← Finsupp.linearCombination_apply]
    rw [← Module.Basis.repr_symm_apply]
    exact (LinearEquiv.symm_apply_apply e.repr x).symm
  rw [hx]
  change (UniversalEnvelopingAlgebra.ι K)
      (∑ i ∈ (e.repr x).support, (e.repr x) i • e i) ∈ S
  rw [map_sum (UniversalEnvelopingAlgebra.ι K)]
  simp only [map_smul]
  refine Submodule.sum_mem S ?_
  intro i hi
  exact S.smul_mem (e.repr x i) (hgen i)

/-- `pbwspan_spanAll` is closed under multiplication. -/
lemma pbwspan_spanAll_mul (e : Module.Basis ι K L) :
    ∀ a ∈ pbwspan_spanAll e, ∀ b ∈ pbwspan_spanAll e, a * b ∈ pbwspan_spanAll e := by
  intro a ha b hb
  refine Submodule.span_induction (p := fun x _ => x * b ∈ pbwspan_spanAll e) ?_ ?_ ?_ ?_ ha
  · intro x hx
    rcases hx with ⟨w, rfl⟩
    refine Submodule.span_induction (p := fun y _ => pbwspan_stWord e w * y ∈ pbwspan_spanAll e)
      ?_ ?_ ?_ ?_ hb
    · intro y hy
      rcases hy with ⟨v, rfl⟩
      apply Submodule.subset_span
      exact ⟨w ++ v, by simp [pbwspan_stWord_append]⟩
    · simp
    · intro x y hx hy hpx hpy
      rw [mul_add]
      exact (pbwspan_spanAll e).add_mem hpx hpy
    · intro c x hx hpx
      rw [mul_smul_comm]
      exact (pbwspan_spanAll e).smul_mem c hpx
  · simp
  · intro x y hx hy hpx hpy
    rw [add_mul]
    exact (pbwspan_spanAll e).add_mem hpx hpy
  · intro c x hx hpx
    rw [smul_mul_assoc]
    exact (pbwspan_spanAll e).smul_mem c hpx

/-- `pbwspan_spanAll` is a subalgebra containing the image of `ι`, hence everything. -/
lemma pbwspan_spanAll_eq_top (e : Module.Basis ι K L) : pbwspan_spanAll e = ⊤ := by
  let S : Submodule K (UniversalEnvelopingAlgebra K L) := pbwspan_spanAll e
  let SAlg : Subalgebra K (UniversalEnvelopingAlgebra K L) :=
    { carrier := (S : Set (UniversalEnvelopingAlgebra K L))
      mul_mem' := by
        intro a b ha hb
        exact pbwspan_spanAll_mul e a ha b hb
      one_mem' := pbwspan_spanAll_one_mem e
      add_mem' := by
        intro a b ha hb
        exact S.add_mem ha hb
      zero_mem' := S.zero_mem
      algebraMap_mem' := by
        intro r
        change algebraMap K (UniversalEnvelopingAlgebra K L) r ∈ S
        simpa [Algebra.algebraMap_eq_smul_one] using S.smul_mem r (pbwspan_spanAll_one_mem e) }
  have hle : Algebra.adjoin K (Set.range (fun x : L => UniversalEnvelopingAlgebra.ι K x)) ≤ SAlg := by
    apply Algebra.adjoin_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact pbwspan_iota_mem e y S (pbwspan_spanAll_basis_mem e)
  have htop : (⊤ : Subalgebra K (UniversalEnvelopingAlgebra K L)) ≤ SAlg := by
    rw [← pbwspan_uea_adjoin_range_ι (K := K) (L := L)]
    exact hle
  ext x
  constructor
  · intro hx
    trivial
  · intro hx
    change x ∈ SAlg
    exact htop hx

/-- Every element of the universal enveloping algebra lies in the span of the `ι`-images of the
basis vectors over all (finite, arbitrary-order) words. -/
lemma pbwspan_stWordSpan_top (e : Module.Basis ι K L) :
    Submodule.span K (pbwspan_allSet e) = ⊤ := by
  exact pbwspan_spanAll_eq_top e


/-- A word is *sorted* if it is nondecreasing. -/
def pbwspan_sorted (w : List ι) : Prop :=
  w.Pairwise (fun a b : ι => a ≤ b)

/-- Number of inversions of a word: pairs `i < j` with `w[i] > w[j]`. -/
def pbwspan_inv : List ι → ℕ
  | [] => 0
  | a :: t => (t.filter (fun b => a > b)).length + pbwspan_inv t

/-- Pairs `(a ∈ u) (b ∈ v)` with `a > b`. -/
def pbwspan_cross : List ι → List ι → ℕ
  | [], _ => 0
  | a :: u, v => (v.filter (fun b => a > b)).length + pbwspan_cross u v

lemma pbwspan_cross_append_left (u1 u2 v : List ι) :
    pbwspan_cross (u1 ++ u2) v = pbwspan_cross u1 v + pbwspan_cross u2 v := by
  induction u1 with
  | nil => simp [pbwspan_cross]
  | cons a u1 ih => simp [pbwspan_cross, ih, Nat.add_assoc]

lemma pbwspan_cross_append_right (u v1 v2 : List ι) :
    pbwspan_cross u (v1 ++ v2) = pbwspan_cross u v1 + pbwspan_cross u v2 := by
  induction u with
  | nil => simp [pbwspan_cross]
  | cons a u ih =>
      simp [pbwspan_cross, ih, List.filter_append, List.length_append]
      omega

lemma pbwspan_inv_append (u v : List ι) :
    pbwspan_inv (u ++ v) = pbwspan_inv u + pbwspan_inv v + pbwspan_cross u v := by
  induction u with
  | nil => simp [pbwspan_inv, pbwspan_cross]
  | cons a u ih =>
      simp [pbwspan_inv, ih, List.filter_append, List.length_append, pbwspan_cross]
      omega

lemma pbwspan_inv_pair (x y : ι) : pbwspan_inv [x, y] = if x > y then 1 else 0 := by
  by_cases h : x > y <;> simp [pbwspan_inv, h]

lemma pbwspan_cross_singleton_right (u : List ι) (a : ι) :
    pbwspan_cross u [a] = (u.filter (fun b => b > a)).length := by
  induction u with
  | nil => simp [pbwspan_cross]
  | cons b u ih =>
      by_cases h : b > a <;> simp [pbwspan_cross, ih, h] <;> omega

lemma pbwspan_cross_singleton_comm (u : List ι) (x y : ι) :
    pbwspan_cross u [x, y] = pbwspan_cross u [y, x] := by
  rw [show [x, y] = [x] ++ [y] by rfl, show [y, x] = [y] ++ [x] by rfl]
  rw [pbwspan_cross_append_right, pbwspan_cross_append_right]
  rw [pbwspan_cross_singleton_right, pbwspan_cross_singleton_right]
  omega

lemma pbwspan_cross_pair_comm (x y : ι) (v : List ι) :
    pbwspan_cross [x, y] v = pbwspan_cross [y, x] v := by
  rw [show [x, y] = [x] ++ [y] by rfl, show [y, x] = [y] ++ [x] by rfl]
  rw [pbwspan_cross_append_left, pbwspan_cross_append_left]
  omega

lemma pbwspan_inv_swap_add (x y : ι) (hxy : x > y) (u v : List ι) :
    pbwspan_inv (u ++ y :: x :: v) + 1 = pbwspan_inv (u ++ x :: y :: v) := by
  have hy : u ++ y :: x :: v = (u ++ [y, x]) ++ v := by
    rw [List.append_assoc]
    rfl
  have hx : u ++ x :: y :: v = (u ++ [x, y]) ++ v := by
    rw [List.append_assoc]
    rfl
  rw [hy, hx]
  rw [pbwspan_inv_append (u ++ [y, x]) v, pbwspan_inv_append (u ++ [x, y]) v]
  rw [pbwspan_inv_append u [y, x], pbwspan_inv_append u [x, y]]
  rw [pbwspan_cross_append_left u [y, x] v, pbwspan_cross_append_left u [x, y] v]
  rw [pbwspan_cross_pair_comm, pbwspan_cross_singleton_comm]
  rw [pbwspan_inv_pair x y, pbwspan_inv_pair y x]
  have hxy' : ¬ y > x := by
    exact not_lt_of_ge (le_of_lt hxy)
  simp [hxy, hxy']
  ac_rfl

lemma pbwspan_inv_swap_lt (x y : ι) (hxy : x > y) (u v : List ι) :
    pbwspan_inv (u ++ y :: x :: v) < pbwspan_inv (u ++ x :: y :: v) := by
  rw [← pbwspan_inv_swap_add x y hxy u v]
  omega

lemma pbwspan_length_swap (x y : ι) (u v : List ι) :
    (u ++ y :: x :: v).length = (u ++ x :: y :: v).length := by
  simp [List.length_append]

/-- Measure `(length, inversions)` on words. -/
def pbwspan_μ (w : List ι) : ℕ × ℕ := (w.length, pbwspan_inv w)

/-- Lexicographic measure decrease. -/
def pbwspan_Rel (w₁ w₂ : List ι) : Prop :=
  Prod.Lex (fun a b : ℕ => a < b) (fun a b : ℕ => a < b) (pbwspan_μ w₁) (pbwspan_μ w₂)

lemma pbwspan_Rel_of_eq_len {w₁ w₂ : List ι} (hlen : w₁.length = w₂.length)
    (hinv : pbwspan_inv w₁ < pbwspan_inv w₂) : pbwspan_Rel w₁ w₂ := by
  unfold pbwspan_Rel pbwspan_μ
  rw [hlen]
  exact Prod.Lex.right w₂.length hinv

lemma pbwspan_Rel_of_len_lt {w₁ w₂ : List ι} (h : w₁.length < w₂.length) :
    pbwspan_Rel w₁ w₂ := by
  exact Prod.Lex.left (pbwspan_inv w₁) (pbwspan_inv w₂) h

lemma pbwspan_Rel_swap (x y : ι) (hxy : x > y) (u v : List ι) :
    pbwspan_Rel (u ++ y :: x :: v) (u ++ x :: y :: v) := by
  apply pbwspan_Rel_of_eq_len
  · exact pbwspan_length_swap x y u v
  · exact pbwspan_inv_swap_lt x y hxy u v

lemma pbwspan_len_delete (u v : List ι) (k x y : ι) :
    (u ++ k :: v).length < (u ++ x :: y :: v).length := by
  simp [List.length_append]

/-- Expanding the bracket of two basis vectors in the basis. -/
lemma pbwspan_iota_bracket_expand (e : Module.Basis ι K L) (x y : ι) :
    UniversalEnvelopingAlgebra.ι K ⁅e x, e y⁆ =
      (e.repr ⁅e x, e y⁆).sum
        (fun k d => d • UniversalEnvelopingAlgebra.ι K (e k)) := by
  let c : ι →₀ K := e.repr ⁅e x, e y⁆
  have hsum : ⁅e x, e y⁆ = c.sum (fun k d => d • e k) := by
    dsimp [c]
    rw [← Finsupp.linearCombination_apply]
    rw [← Module.Basis.repr_symm_apply]
    exact (LinearEquiv.symm_apply_apply e.repr ⁅e x, e y⁆).symm
  have hι : UniversalEnvelopingAlgebra.ι K ⁅e x, e y⁆ =
      c.sum (fun k d => d • UniversalEnvelopingAlgebra.ι K (e k)) := by
    rw [hsum]
    change (UniversalEnvelopingAlgebra.ι K)
        (∑ k ∈ c.support, c k • e k) =
      c.sum (fun k d => d • UniversalEnvelopingAlgebra.ι K (e k))
    rw [map_sum (UniversalEnvelopingAlgebra.ι K)]
    simp only [map_smul]
    rfl
  simpa [c] using hι

/-- Left multiplication distributes over a `Finsupp` sum. -/
lemma pbwspan_mul_sum (a : UniversalEnvelopingAlgebra K L) (f : ι →₀ K)
    (g : ι → K → UniversalEnvelopingAlgebra K L) :
    a * f.sum g = f.sum (fun i c => a * g i c) := by
  change a * (∑ i ∈ f.support, g i (f i)) =
      f.sum (fun i c => a * g i c)
  rw [Finset.mul_sum]
  change (∑ i ∈ f.support, a * g i (f i)) =
      f.sum (fun i c => a * g i c)
  rfl

/-- The product of `ι ⁅e x, e y⁆` with a word product, expanded. -/
lemma pbwspan_iota_bracket_stWord (e : Module.Basis ι K L) (x y : ι) (v : List ι) :
    UniversalEnvelopingAlgebra.ι K ⁅e x, e y⁆ * pbwspan_stWord e v =
      (e.repr ⁅e x, e y⁆).sum (fun k d => d • pbwspan_stWord e (k :: v)) := by
  rw [pbwspan_iota_bracket_expand e x y]
  rw [Finsupp.sum_mul]
  congr 1
  funext k d
  rw [Algebra.smul_mul_assoc]
  rfl

/-- Swapping the head of a word: base case (`u = []`). -/
lemma pbwspan_stWord_swap_nil (e : Module.Basis ι K L) (x y : ι) (v : List ι) :
    pbwspan_stWord e (x :: y :: v) =
      pbwspan_stWord e (y :: x :: v) +
        (e.repr ⁅e x, e y⁆).sum (fun k d => d • pbwspan_stWord e (k :: v)) := by
  calc
    pbwspan_stWord e (x :: y :: v)
        = UniversalEnvelopingAlgebra.ι K (e x) * UniversalEnvelopingAlgebra.ι K (e y) *
            pbwspan_stWord e v := by rw [pbwspan_stWord_cons2]
    _ = (UniversalEnvelopingAlgebra.ι K (e y) * UniversalEnvelopingAlgebra.ι K (e x) +
          UniversalEnvelopingAlgebra.ι K ⁅e x, e y⁆) * pbwspan_stWord e v := by
          rw [pbwspan_iota_swap e x y]
    _ = (UniversalEnvelopingAlgebra.ι K (e y) * UniversalEnvelopingAlgebra.ι K (e x)) *
            pbwspan_stWord e v +
          UniversalEnvelopingAlgebra.ι K ⁅e x, e y⁆ * pbwspan_stWord e v := by
          rw [add_mul]
    _ = pbwspan_stWord e (y :: x :: v) +
          UniversalEnvelopingAlgebra.ι K ⁅e x, e y⁆ * pbwspan_stWord e v := by
          rw [← pbwspan_stWord_cons2]
    _ = pbwspan_stWord e (y :: x :: v) +
          (e.repr ⁅e x, e y⁆).sum (fun k d => d • pbwspan_stWord e (k :: v)) := by
          rw [pbwspan_iota_bracket_stWord e x y v]

/-- Straightening identity for one adjacent swap at position `|u|`. -/
lemma pbwspan_stWord_swap (e : Module.Basis ι K L) (u v : List ι) (x y : ι) :
    pbwspan_stWord e (u ++ x :: y :: v) =
      pbwspan_stWord e (u ++ y :: x :: v) +
        (e.repr ⁅e x, e y⁆).sum (fun k d => d • pbwspan_stWord e (u ++ k :: v)) := by
  induction u with
  | nil =>
      simpa using pbwspan_stWord_swap_nil e x y v
  | cons a u ih =>
      have hsum : UniversalEnvelopingAlgebra.ι K (e a) *
            (e.repr ⁅e x, e y⁆).sum (fun k d => d • pbwspan_stWord e (u ++ k :: v)) =
          (e.repr ⁅e x, e y⁆).sum (fun k d => d • pbwspan_stWord e ((a :: u) ++ k :: v)) := by
        rw [pbwspan_mul_sum]
        apply Finsupp.sum_congr
        intro k hk
        rw [mul_smul_comm]
        rw [← pbwspan_stWord_cons]
        rfl
      calc
        pbwspan_stWord e ((a :: u) ++ x :: y :: v)
            = pbwspan_stWord e (a :: (u ++ x :: y :: v)) := by rfl
        _ = UniversalEnvelopingAlgebra.ι K (e a) * pbwspan_stWord e (u ++ x :: y :: v) := by
            rw [pbwspan_stWord_cons]
        _ = UniversalEnvelopingAlgebra.ι K (e a) *
              (pbwspan_stWord e (u ++ y :: x :: v) +
                (e.repr ⁅e x, e y⁆).sum (fun k d => d • pbwspan_stWord e (u ++ k :: v))) := by
            rw [ih]
        _ = UniversalEnvelopingAlgebra.ι K (e a) * pbwspan_stWord e (u ++ y :: x :: v) +
              UniversalEnvelopingAlgebra.ι K (e a) *
                (e.repr ⁅e x, e y⁆).sum
                  (fun k d => d • pbwspan_stWord e (u ++ k :: v)) := by
            rw [mul_add]
        _ = pbwspan_stWord e (a :: (u ++ y :: x :: v)) +
              (e.repr ⁅e x, e y⁆).sum (fun k d => d • pbwspan_stWord e ((a :: u) ++ k :: v)) := by
            rw [← pbwspan_stWord_cons, hsum]
        _ = pbwspan_stWord e ((a :: u) ++ y :: x :: v) +
              (e.repr ⁅e x, e y⁆).sum (fun k d => d • pbwspan_stWord e ((a :: u) ++ k :: v)) := by
            rfl

lemma pbwspan_wfRel : WellFounded (pbwspan_Rel : List ι → List ι → Prop) := by
  change WellFounded (InvImage (Prod.Lex (fun a b : ℕ => a < b) (fun a b : ℕ => a < b)) pbwspan_μ)
  exact InvImage.wf pbwspan_μ (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)

/-- A non-sorted word has an adjacent descent. -/
lemma pbwspan_descent_of_not_sorted : ∀ w : List ι, ¬ pbwspan_sorted w →
    ∃ (u : List ι) (x y : ι) (v : List ι), x > y ∧ w = u ++ x :: y :: v := by
  intro w
  induction w with
  | nil =>
      intro h
      exact False.elim (h (by simp [pbwspan_sorted]))
  | cons a t ih =>
      intro h
      by_cases ht : pbwspan_sorted t
      · -- `t` is sorted; the failure is at the head
        have hnot : ¬ ∀ b ∈ t, a ≤ b := by
          intro hall
          apply h
          simpa [pbwspan_sorted] using (List.pairwise_cons (a := a) (l := t)).2 ⟨hall, ht⟩
        have htne : t ≠ [] := by
          intro hnil
          apply hnot
          intro b hb
          simpa [hnil] using hb
        rcases List.exists_cons_of_ne_nil htne with ⟨c, rest, rfl⟩
        have hnot' : ¬ ∀ b ∈ (c :: rest), a ≤ b := by
          intro hall
          apply hnot
          intro b hb
          exact hall b hb
        have hac : ¬ a ≤ c := by
          intro hac
          apply hnot'
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hbr
          · exact hac
          · exact le_trans hac (List.rel_of_pairwise_cons ht hbr)
        refine ⟨[], a, c, rest, lt_of_not_ge hac, rfl⟩
      · -- the descent lies inside `t`
        rcases ih ht with ⟨u, x, y, v, hxy, ht_eq⟩
        refine ⟨a :: u, x, y, v, hxy, ?_⟩
        simp [ht_eq]
/-- Every word product lies in the span of the standard monomials (straightening). -/
lemma pbwspan_stWord_mem_spanStd (e : Module.Basis ι K L) :
    ∀ w : List ι, pbwspan_stWord e w ∈ pbwspan_spanStd e := by
  intro w
  refine pbwspan_wfRel.induction (C := fun x => pbwspan_stWord e x ∈ pbwspan_spanStd e) w ?_
  intro x ih
  by_cases hs : pbwspan_sorted x
  · apply Submodule.subset_span
    exact ⟨⟨x, hs⟩, rfl⟩
  · rcases pbwspan_descent_of_not_sorted x hs with ⟨u, a, b, v, hab, hx⟩
    subst x
    rw [pbwspan_stWord_swap e u v a b]
    apply (pbwspan_spanStd e).add_mem
    · exact ih (u ++ b :: a :: v) (pbwspan_Rel_swap a b hab u v)
    · change (∑ k ∈ (e.repr ⁅e a, e b⁆).support,
          (e.repr ⁅e a, e b⁆) k • pbwspan_stWord e (u ++ k :: v)) ∈ pbwspan_spanStd e
      refine Submodule.sum_mem (pbwspan_spanStd e) ?_
      intro k hk
      exact (pbwspan_spanStd e).smul_mem (e.repr ⁅e a, e b⁆ k)
        (ih (u ++ k :: v) (pbwspan_Rel_of_len_lt (pbwspan_len_delete u v k a b)))

end PBWSpanning

theorem standardMonomial_spanning (K L ι : Type u) [Field K] [CharZero K]
    [LieRing L] [LieAlgebra K L] [LinearOrder ι]
    (e : Module.Basis ι K L) :
    Submodule.span K
        {x : UniversalEnvelopingAlgebra K L |
          ∃ w : {w : List ι // w.Pairwise (fun a b : ι => a ≤ b)},
            x = (w.1.map (fun i => UniversalEnvelopingAlgebra.ι K (e i))).prod} =
      ⊤ := by
  change Submodule.span K (pbwspan_stdSet e) = ⊤
  have hall : Submodule.span K (pbwspan_allSet e) = ⊤ := pbwspan_spanAll_eq_top e
  have hmono : pbwspan_stdSet e ⊆ pbwspan_allSet e := by
    intro x hx
    rcases hx with ⟨w, rfl⟩
    exact ⟨w.1, rfl⟩
  have hstd_le_all : Submodule.span K (pbwspan_stdSet e) ≤ Submodule.span K (pbwspan_allSet e) :=
    Submodule.span_mono hmono
  have hall_le_std : Submodule.span K (pbwspan_allSet e) ≤ Submodule.span K (pbwspan_stdSet e) := by
    rw [Submodule.span_le]
    intro x hx
    rcases hx with ⟨w, rfl⟩
    exact pbwspan_stWord_mem_spanStd e w
  apply le_antisymm
  · intro x hx
    trivial
  · calc
      (⊤ : Submodule K (UniversalEnvelopingAlgebra K L)) ≤ Submodule.span K (pbwspan_allSet e) := by
        rw [← hall]
      _ ≤ Submodule.span K (pbwspan_stdSet e) := hall_le_std

end Commons.Algebra.Lie.PBW