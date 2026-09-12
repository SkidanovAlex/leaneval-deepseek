import Mathlib
import Submission.Szemeredi.Corners
import Submission.Szemeredi.Roth
import Submission.Commons.Combinatorics.Additive.AP.exists_ap_of_cyclic_consecutive

/-!
# From the multidimensional corners theorem to Szemerédi

The main content: `finiteSzemeredi_of_cornersD`.

## Strategy (classical)

Fix the progression length `k = n + 2 ≥ 2` (so `n + 1` coordinates).  Given a
dense set `A ⊆ {0,…,N-1}` we need a `k`-term progression.  Let `M = 2N + 1`
and embed `A` in the cyclic group `ZMod M`.  On the vector space
`V = (Fin (n+1) → ZMod M)` define the linear form

    cornerMap x = ∑ᵢ (i.val + 1) • x i .

Let `B = {x : V | cornerMap x ∈ A'}` where `A'` is the image of `A` in `ZMod M`.
Every fiber of `cornerMap` over an element of `A'` has `Mⁿ` elements (the first
coordinate is determined by the rest), so `|B| ≥ |A| · Mⁿ ≥ (δ/4) · Mⁿ⁺¹` for
`N ≥ 1`.  The corners theorem (dimension `n+1`, density `δ/4`) supplies a
corner `{x} ∪ {x + t·eᵢ}` inside `B`.  Evaluating `cornerMap` on the `n+2`
points of the corner yields the group elements

    cornerMap x + j • t   (j = 0, 1, …, n+1)

all lying in `A'`.  Since every element of `A'` has a representative in
`{0,…,N-1}` and `M = 2N+1`, the difference between two consecutive
representatives is a fixed nonzero integer strictly between `-N` and `N`, so
the representatives are exactly the terms `a + j·d` of an arithmetic
progression of length `n+2` inside `A` — the desired progression.
-/

open scoped BigOperators
open Finset

namespace Szemeredi

/-- Non-dependent `Fin.cons`: prepend `x₀` to the tuple `y : Fin n → G`.  (Unlike
the dependent `Fin.cons`, applications of `ncons` elaborate without typeclass
guessing, since the result type is fixed.) -/
def ncons {n : ℕ} {G : Type*} (x₀ : G) (y : Fin n → G) : Fin (n + 1) → G :=
  fun i => Fin.cases (motive := fun _ : Fin (n + 1) => G) x₀ y i

@[simp] lemma ncons_zero {n : ℕ} {G : Type*} (x₀ : G) (y : Fin n → G) :
    ncons x₀ y 0 = x₀ := by
  simp [ncons]

@[simp] lemma ncons_succ {n : ℕ} {G : Type*} (x₀ : G) (y : Fin n → G) (j : Fin n) :
    ncons x₀ y j.succ = y j := by
  simp [ncons]

lemma ncons_injective {n : ℕ} {G : Type*} : Function.Injective2 (ncons : G → (Fin n → G) → Fin (n + 1) → G) := by
  intro x₀ x₀' y y' h
  have h0 := congrFun h 0
  have hsucc : ∀ j : Fin n, y j = y' j := by
    intro j
    have hj := congrFun h j.succ
    simpa using hj
  refine ⟨?_, ?_⟩
  · simpa using h0
  · funext j
    exact hsucc j

section CornerMap

variable {G : Type*} [AddCommGroup G]

/-- The weighted coordinate sum `∑ᵢ (i.val + 1) • xᵢ` (coordinates `0,…,n`
carry weights `1,…,n+1`). -/
def cornerMap {n : ℕ} (x : Fin (n + 1) → G) : G :=
  ∑ i : Fin (n + 1), ((i.val + 1 : ℕ) • x i)

/-- Moving the corner by `t` in direction `i`: coordinate `i` increases by `t`. -/
def cornerAxis {n : ℕ} (x : Fin (n + 1) → G) (i : Fin (n + 1)) (t : G) : Fin (n + 1) → G :=
  fun j => x j + if j = i then t else 0

lemma cornerMap_axis {n : ℕ} (x : Fin (n + 1) → G) (i : Fin (n + 1)) (t : G) :
    cornerMap (cornerAxis x i t) = cornerMap x + ((i.val + 1 : ℕ) • t) := by
  unfold cornerMap cornerAxis
  calc
    (∑ j : Fin (n + 1), ((j.val + 1 : ℕ) • (x j + if j = i then t else 0)))
        = ∑ j : Fin (n + 1), (((j.val + 1 : ℕ) • x j) + ((j.val + 1 : ℕ) • (if j = i then t else 0))) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [nsmul_add]
    _ = (∑ j : Fin (n + 1), ((j.val + 1 : ℕ) • x j))
          + ∑ j : Fin (n + 1), ((j.val + 1 : ℕ) • (if j = i then t else 0)) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ j : Fin (n + 1), ((j.val + 1 : ℕ) • x j))
          + ((i.val + 1 : ℕ) • t) := by
          congr 1
          calc
            (∑ x : Fin (n + 1), ((x.val + 1 : ℕ) • (if x = i then t else 0)))
                = ∑ x : Fin (n + 1), (if x = i then ((x.val + 1 : ℕ) • t) else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro x _
                  by_cases hxi : x = i <;> simp [hxi]
            _ = ((i.val + 1 : ℕ) • t) := by
                  rw [Finset.sum_ite_eq']
                  simp
lemma cornerMap_add {n : ℕ} (x y : Fin (n + 1) → G) :
    cornerMap (x + y) = cornerMap x + cornerMap y := by
  unfold cornerMap
  calc
    (∑ i : Fin (n + 1), ((i.val + 1 : ℕ) • (x + y) i))
        = ∑ i : Fin (n + 1), (((i.val + 1 : ℕ) • x i) + ((i.val + 1 : ℕ) • y i)) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Pi.add_apply, nsmul_add]
    _ = (∑ i : Fin (n + 1), ((i.val + 1 : ℕ) • x i))
          + (∑ i : Fin (n + 1), ((i.val + 1 : ℕ) • y i)) := by
          rw [Finset.sum_add_distrib]

lemma cornerMap_zero {n : ℕ} : cornerMap (0 : Fin (n + 1) → G) = 0 := by
  simp [cornerMap]

/-- The value of `cornerMap` on a vector written as `(x₀, y)`:
only the leading coordinate and the weighted rest remain. -/
lemma cornerMap_ncons {n : ℕ} (x₀ : G) (y : Fin n → G) :
    cornerMap (ncons x₀ y) = x₀ + ∑ j : Fin n, ((j.val + 2 : ℕ) • y j) := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  unfold cornerMap
  rw [Fin.sum_univ_succ]
  have h0 : ((0 : Fin (n + 1)).val + 1 : ℕ) • ncons x₀ y 0 = x₀ := by
    rw [ncons_zero]
    have hc : (0 : Fin (n + 1)).val + 1 = 1 := by simp
    rw [hc]
    simp
  rw [h0]
  refine congrArg (fun s : G => x₀ + s) ?_
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [ncons_succ]
  apply congrArg (fun c : ℕ => c • y j)
  rw [Fin.val_succ]
end CornerMap

section Cyclic

/-- Injectivity of the natural cast into `ZMod` below the modulus. -/
private lemma natCast_zmod_inj_of_lt {M a b : ℕ} [NeZero M] (ha : a < M) (hb : b < M)
    (h : (a : ZMod M) = (b : ZMod M)) : a = b := by
  have hva := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_natCast] at hva
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hva
  exact hva

/-- The weighted sum over the `n` free coordinates `y` in the fibre description of
`cornerMap`: coordinate `j.succ` of a vector carries weight `j.val + 2`. -/
noncomputable def tailSum (N : ℕ) {n : ℕ} (y : Fin n → ZMod (2 * N + 1)) : ZMod (2 * N + 1) :=
  ∑ j : Fin n, ((j.val + 2 : ℕ) • y j)

lemma cornerMap_ncons_tailSum (N : ℕ) {n : ℕ} (x₀ : ZMod (2 * N + 1))
    (y : Fin n → ZMod (2 * N + 1)) : cornerMap (ncons x₀ y) = x₀ + tailSum N y := by
  rw [tailSum]
  exact cornerMap_ncons x₀ y

/-- The vector with `cornerMap` equal to the image of `a`, free coordinates `y`. -/
noncomputable def cornerFiber (N : ℕ) {n : ℕ} (a : ℕ) (y : Fin n → ZMod (2 * N + 1)) :
    Fin (n + 1) → ZMod (2 * N + 1) :=
  ncons ((a : ZMod (2 * N + 1)) - tailSum N y) y

lemma cornerMap_cornerFiber (N : ℕ) {n : ℕ} (a : ℕ) (y : Fin n → ZMod (2 * N + 1)) :
    cornerMap (cornerFiber N a y) = (a : ZMod (2 * N + 1)) := by
  unfold cornerFiber
  rw [cornerMap_ncons_tailSum]
  abel

/-- The dense set: all vectors whose `cornerMap` lies in the embedded image of `A`. -/
noncomputable def cornerSet (N : ℕ) {n : ℕ} (A : Finset ℕ) : Finset (Fin (n + 1) → ZMod (2 * N + 1)) := by
  classical
  exact Finset.univ.filter (fun x => cornerMap x ∈ A.image (fun a : ℕ => (a : ZMod (2 * N + 1))))

lemma mem_cornerSet (N : ℕ) {n : ℕ} (A : Finset ℕ) (x : Fin (n + 1) → ZMod (2 * N + 1)) :
    x ∈ cornerSet N A ↔ cornerMap x ∈ A.image (fun a : ℕ => (a : ZMod (2 * N + 1))) := by
  classical
  simp [cornerSet]

lemma cornerFiber_mem_cornerSet (N : ℕ) {n : ℕ} {A : Finset ℕ} {a : ℕ} (ha : a ∈ A)
    (y : Fin n → ZMod (2 * N + 1)) : cornerFiber N a y ∈ cornerSet N A := by
  classical
  rw [mem_cornerSet, cornerMap_cornerFiber]
  exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

/-- `cornerFiber` is injective on `A` (with its natural bounds) times the free coordinates. -/
lemma cornerFiber_injOn (N : ℕ) {n : ℕ} {A : Finset ℕ} (hAsub : A ⊆ Finset.range N) :
    Set.InjOn (fun p : ℕ × (Fin n → ZMod (2 * N + 1)) => cornerFiber N p.1 p.2)
      ((A : Set ℕ) ×ˢ Set.univ) := by
  haveI : NeZero (2 * N + 1) := ⟨by omega⟩
  intro p hp q hq hpq
  rcases p with ⟨a, y⟩
  rcases q with ⟨b, z⟩
  change cornerFiber N a y = cornerFiber N b z at hpq
  unfold cornerFiber at hpq
  have hcons := ncons_injective (G := ZMod (2 * N + 1)) hpq
  rcases hcons with ⟨hx, hyz⟩
  have ha : a < N := Finset.mem_range.mp (hAsub hp.1)
  have hb : b < N := Finset.mem_range.mp (hAsub hq.1)
  have hcast : (a : ZMod (2 * N + 1)) = (b : ZMod (2 * N + 1)) := by
    have hx' : (a : ZMod (2 * N + 1)) - tailSum N y = (b : ZMod (2 * N + 1)) - tailSum N z := hx
    rw [hyz] at hx'
    have hx'' := congrArg (fun s : ZMod (2 * N + 1) => s + tailSum N y) hx'
    simpa [sub_add_cancel, add_assoc] using hx''
  have hab : a = b := natCast_zmod_inj_of_lt (M := 2 * N + 1) (by omega) (by omega) hcast
  refine Prod.ext ?_ ?_
  · exact hab
  · ext j
    exact congrFun hyz j

/-- Lower bound on the size of the dense corner set:
`|cornerSet N A| ≥ |A| · (2N+1)ⁿ` whenever `A ⊆ range N`. -/
lemma cornerSet_card_ge (N : ℕ) {n : ℕ} {A : Finset ℕ} (hAsub : A ⊆ Finset.range N) :
    A.card * (2 * N + 1) ^ n ≤ (cornerSet (n := n) N A).card := by
  classical
  haveI : NeZero (2 * N + 1) := ⟨by omega⟩
  have hM : Fintype.card (ZMod (2 * N + 1)) = 2 * N + 1 := ZMod.card (2 * N + 1)
  let Φ : ℕ × (Fin n → ZMod (2 * N + 1)) → Fin (n + 1) → ZMod (2 * N + 1) :=
    fun p => cornerFiber N p.1 p.2
  let S : Finset (ℕ × (Fin n → ZMod (2 * N + 1))) := A.product (Finset.univ)
  have hsubset : S.image Φ ⊆ cornerSet (n := n) N A := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    exact cornerFiber_mem_cornerSet N (Finset.mem_product.mp hp).1 p.2
  have hcardS : S.card = A.card * (2 * N + 1) ^ n := by
    dsimp [S]
    rw [Finset.card_product]
    rw [Finset.card_univ, Fintype.card_fun]
    simp [hM]
  calc
    A.card * (2 * N + 1) ^ n = S.card := by rw [hcardS]
    _ = (S.image Φ).card := by
      rw [Finset.card_image_of_injOn]
      simpa [S] using (cornerFiber_injOn N hAsub)
    _ ≤ (cornerSet (n := n) N A).card := Finset.card_le_card hsubset

end Cyclic

section CornerValues

/-- The values of `cornerMap` on the `n+2` corner points, indexed `j = 0..n+1`. -/
noncomputable def cornerValues {n : ℕ} {G : Type*} [AddCommGroup G]
    (x : Fin (n + 1) → G) (t : G) : Fin (n + 2) → G :=
  fun j => cornerMap x + (j.val : ℕ) • t

/-- All `n+2` values of `cornerMap` on the points `{x} ∪ {x + t·eᵢ}` lie in the
embedded image of `A`, whenever all those points lie in the `cornerSet`. -/
lemma corner_values_mem {n N : ℕ} {A : Finset ℕ} {x : Fin (n + 1) → ZMod (2 * N + 1)}
    {t : ZMod (2 * N + 1)}
    (hxB : x ∈ cornerSet N A)
    (haxis : ∀ i : Fin (n + 1), cornerAxis x i t ∈ cornerSet N A) :
    ∀ j : Fin (n + 2),
      cornerValues x t j ∈ A.image (fun a : ℕ => (a : ZMod (2 * N + 1))) := by
  classical
  intro j
  cases j using Fin.cases with
  | zero =>
      have h0 : cornerValues x t 0 = cornerMap x := by
        haveI : NeZero (n + 2) := ⟨by omega⟩
        simp [cornerValues]
      rw [h0]
      exact (mem_cornerSet N A x).mp hxB
  | succ i =>
      have hval : cornerValues x t i.succ = cornerMap (cornerAxis x i t) := by
        rw [cornerValues, Fin.val_succ]
        exact (cornerMap_axis x i t).symm
      rw [hval]
      have haxis' : cornerAxis x i t ∈ cornerSet N A := by
        simpa using haxis i
      exact (mem_cornerSet N A (cornerAxis x i t)).mp haxis'

/-- A corner in the dense `cornerSet` yields a `(n+2)`-term progression inside `A`
(the corner evaluates, via `cornerMap`, to `n+2` consecutive shifts of one element,
whose representatives in `{0,…,N-1}` form the progression). -/
lemma hasAP_of_cornerD {n N : ℕ} {A : Finset ℕ} (hAsub : A ⊆ Finset.range N)
    {x : Fin (n + 1) → ZMod (2 * N + 1)} {t : ZMod (2 * N + 1)}
    (hcorner : IsCornerD (cornerSet (n := n) N A : Set (Fin (n + 1) → ZMod (2 * N + 1))) x t) :
    HasAP (A : Set ℕ) (n + 2) := by
  classical
  haveI : NeZero (2 * N + 1) := ⟨by omega⟩
  have hxB : x ∈ cornerSet (n := n) N A := by simpa using hcorner.2.1
  have haxis : ∀ i : Fin (n + 1), cornerAxis x i t ∈ cornerSet (n := n) N A := hcorner.2.2
  have ht0 : t ≠ 0 := hcorner.1
  let g : Fin (n + 2) → ZMod (2 * N + 1) := cornerValues x t
  have hg : ∀ j : Fin (n + 2),
      g j ∈ A.image (fun a : ℕ => (a : ZMod (2 * N + 1))) := by
    intro j
    exact corner_values_mem hxB haxis j
  let a : Fin (n + 2) → ℕ := fun j => Classical.choose (Finset.mem_image.mp (hg j))
  have haA : ∀ j : Fin (n + 2), a j ∈ A := by
    intro j
    exact (Classical.choose_spec (Finset.mem_image.mp (hg j))).1
  have haG : ∀ j : Fin (n + 2), (a j : ZMod (2 * N + 1)) = g j := by
    intro j
    exact (Classical.choose_spec (Finset.mem_image.mp (hg j))).2
  have haN : ∀ j : Fin (n + 2), a j < N := by
    intro j
    exact Finset.mem_range.mp (hAsub (haA j))
  have hstep : ∀ j : Fin (n + 1),
      ((a j.succ : ℤ) - (a (j.castSucc : Fin (n + 2)) : ℤ) : ZMod (2 * N + 1)) = t := by
    intro j
    have hid : (((a j.succ : ℤ) - (a (j.castSucc : Fin (n + 2)) : ℤ) : ZMod (2 * N + 1)))
        = ((a j.succ : ZMod (2 * N + 1)) - (a (j.castSucc : Fin (n + 2)) : ZMod (2 * N + 1))) := by
      simp
    rw [hid, haG, haG]
    -- g (j.succ) - g (j.castSucc) = t
    have hdiff : g j.succ - g (j.castSucc : Fin (n + 2)) = t := by
      dsimp [g, cornerValues]
      rw [show ((j.val + 1 : ℕ) • t) = ((j.val : ℕ) • t + t) by
        simpa [one_nsmul] using (add_nsmul t j.val 1)]
      abel
    exact hdiff
  -- final step: representatives in `A` with pairwise-congruent consecutive differences
  -- form a `(n+2)`-term progression (see the lemma in the shared commons).
  obtain ⟨c, b, hb, hAP⟩ :=
    Commons.Combinatorics.Additive.AP.exists_ap_of_cyclic_consecutive (A := A) a haA haN t ht0 hstep
  exact ⟨c, b, hb, fun j hj => by simpa using hAP j hj⟩



/-- **Main reduction.**  If the `(n+1)`-dimensional corners theorem holds at density
`δ/4` (for the cyclic group `ZMod (2N+1)` of every large enough `N`), then every
`δ`-dense subset of `{0,…,N-1}` (`N` large) contains a `(n+2)`-term progression. -/
theorem finiteSzemeredi_of_cornersD {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hcor : CornersFiniteD (n + 1) (δ / 4)) : FiniteSzemeredi (n + 2) δ := by
  classical
  rcases hcor with ⟨N₀, hN₀⟩
  refine ⟨max N₀ 1, ?_⟩
  intro N hN A hAsub hAδ
  have hN0 : N₀ ≤ N := le_trans (le_max_left N₀ 1) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right N₀ 1) hN
  haveI : NeZero (2 * N + 1) := ⟨by omega⟩
  let B : Finset (Fin (n + 1) → ZMod (2 * N + 1)) := cornerSet N A
  have hBcard : (A.card : ℝ) * (((2 * N + 1 : ℕ) : ℝ) ^ n) ≤ (B.card : ℝ) := by
    exact_mod_cast (cornerSet_card_ge N hAsub)
  have hM4 : (((2 * N + 1 : ℕ) : ℝ) / 4) ≤ (N : ℝ) := by
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    norm_num [Nat.cast_add, Nat.cast_mul]
    nlinarith
  have hmain : (δ / 4) * ((2 * N + 1 : ℕ) : ℝ) ≤ δ * (N : ℝ) := by
    rw [show (δ / 4) * (((2 * N + 1 : ℕ) : ℝ)) = δ * ((((2 * N + 1 : ℕ) : ℝ)) / 4) by ring]
    exact mul_le_mul_of_nonneg_left hM4 (le_of_lt hδ)
  have hle1 : (δ / 4) * (((2 * N + 1 : ℕ) : ℝ) ^ (n + 1))
      ≤ δ * (N : ℝ) * (((2 * N + 1 : ℕ) : ℝ) ^ n) := by
    calc
      (δ / 4) * (((2 * N + 1 : ℕ) : ℝ) ^ (n + 1))
          = (δ / 4) * ((2 * N + 1 : ℕ) : ℝ) * (((2 * N + 1 : ℕ) : ℝ) ^ n) := by
            rw [pow_succ]
            ring
      _ ≤ δ * (N : ℝ) * (((2 * N + 1 : ℕ) : ℝ) ^ n) := by
            exact mul_le_mul_of_nonneg_right hmain (pow_nonneg (by positivity) n)
  have hBd : (δ / 4) * (((2 * N + 1 : ℕ) : ℝ) ^ (n + 1)) ≤ (B.card : ℝ) := by
    calc
      (δ / 4) * (((2 * N + 1 : ℕ) : ℝ) ^ (n + 1))
          ≤ δ * (N : ℝ) * (((2 * N + 1 : ℕ) : ℝ) ^ n) := hle1
      _ ≤ (A.card : ℝ) * (((2 * N + 1 : ℕ) : ℝ) ^ n) := by
            exact mul_le_mul_of_nonneg_right hAδ (pow_nonneg (by positivity) n)
      _ ≤ (B.card : ℝ) := hBcard
  obtain ⟨x, t, hcorn⟩ := hN₀ (2 * N + 1) (by omega) (by omega) B hBd
  exact hasAP_of_cornerD hAsub hcorn

/-- The whole finite Szemerédi theorem (every length, every density) follows from the
`d`-dimensional cyclic corners theorem at every dimension `d` and density. -/
theorem finite_szemeredi_of_corners_allD
    (hcorn : ∀ (d : ℕ) (ε : ℝ), 0 < ε → CornersFiniteD d ε) :
    ∀ (k : ℕ) (δ : ℝ), 0 < δ → FiniteSzemeredi k δ := by
  intro k δ hδ
  by_cases hk : k ≤ 3
  · interval_cases k
    · exact finiteSzemeredi_zero δ hδ
    · exact finiteSzemeredi_one δ hδ
    · exact finiteSzemeredi_two δ hδ
    · exact finiteSzemeredi_three δ hδ
  · -- k ≥ 4, so k = (k - 2) + 2 and dimension d = k - 1 = (k-2) + 1
    have hd : 0 < δ / 4 := by positivity
    have hc : CornersFiniteD (k - 1) (δ / 4) := hcorn (k - 1) (δ / 4) hd
    have hk' : k - 1 = (k - 2) + 1 := by omega
    have hk'' : k = (k - 2) + 2 := by omega
    have hc' : CornersFiniteD ((k - 2) + 1) (δ / 4) := by
      rw [← hk']
      exact hc
    rw [hk'']
    exact finiteSzemeredi_of_cornersD (n := k - 2) hδ hc'

end CornerValues
end Szemeredi
