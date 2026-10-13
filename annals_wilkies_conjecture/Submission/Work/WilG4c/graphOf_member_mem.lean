import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG0.API
import Submission.Work.WilG1.Basic
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex3

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ### A coordinate hyperplane is `Ω`-definable with degree one

`{z | z i = c}` is cut out by the *linear* polynomial `X i - C c`, so its `Ω`-degree is `1`
(uniformly in the constant `c`, hence uniformly in the parameter value).  This is the
sharp version of `Work.WilG1.Thin.coordEqSet_mem`, which only records degree `D + 1`; the
sharpness is what makes the sliced family below cost only an *additive* constant in the
degree. -/
theorem coordEqSet_mem_deg1 {S : SOMin} {n : ℕ} (i : Fin n) (c : ℝ) :
    {z : Fin n → ℝ | z i = c} ∈ S.Ω n 1 n := by
  have h := S.hyp n (MvPolynomial.X i - MvPolynomial.C c : MvPolynomial (Fin n) ℝ)
  have hset : {z : Fin n → ℝ | MvPolynomial.eval z
      (MvPolynomial.X i - MvPolynomial.C c : MvPolynomial (Fin n) ℝ) = 0}
      = {z : Fin n → ℝ | z i = c} := by
    ext z
    simp [MvPolynomial.eval_sub, MvPolynomial.eval_C, sub_eq_zero]
  rw [hset] at h
  refine Work.WilG5.mem_mono h n 1 le_rfl ?_
  refine le_trans (Work.WilG5.td_sub_le _ _) (max_le ?_ ?_)
  · exact Work.WilG5.td_X_le i
  · exact le_trans (Work.WilG5.td_C_le c) (Nat.zero_le 1)

/-- The index map selecting the trailing `m+1` coordinates of `Fin (p+m+1)`. -/
def sidx (p m : ℕ) : Fin (m + 1) → Fin (p + m + 1) := fun k => Fin.natAdd p k

/-! ### The `Fin`-arithmetic behind the slicing

Reading `ℝ^{p+m+1}` as `(x, u, y)` with `x` the first `p` coordinates, the trailing block
`Fin.append x v = (x, v)` has initial part `Fin.append x (Fin.init v)`: the value coordinate
is dropped by `Fin.init`. -/
theorem fin_init_append {p m : ℕ} (x : Fin p → ℝ) (v : Fin (m + 1) → ℝ) :
    Fin.init ((Fin.append (m := p) (n := m + 1) x v) : Fin (p + m + 1) → ℝ)
      = (Fin.append x (Fin.init v) : Fin (p + m) → ℝ) := by
  funext j
  induction j using Fin.addCases with
  | left i =>
      show (Fin.append (m := p) (n := m + 1) x v) (Fin.castAdd m i).castSucc
        = Fin.append x (Fin.init v) (Fin.castAdd m i)
      rw [show (Fin.castAdd m i).castSucc = (Fin.castAdd (m + 1) i : Fin (p + m + 1)) from
        Fin.ext (by simp)]
      rw [Fin.append_left, Fin.append_left]
  | right k =>
      show (Fin.append (m := p) (n := m + 1) x v) (Fin.natAdd p k).castSucc
        = Fin.append x (Fin.init v) (Fin.natAdd p k)
      rw [show (Fin.natAdd p k).castSucc = (Fin.natAdd p k.castSucc : Fin (p + (m + 1))) from
        (Fin.natAdd_castSucc (n := p) (i := k)).symm]
      rw [Fin.append_right, Fin.append_right]
      rfl

/-- Conversely, knowing that `z` agrees with `x` on the first `p` coordinates and that the
trailing block `z ∘ sidx` is `v`, the initial part of `z` is `Fin.append x (Fin.init v)`. -/
theorem fin_init_eq_append_of {p m : ℕ} {z : Fin (p + m + 1) → ℝ} {v : Fin (m + 1) → ℝ}
    {x : Fin p → ℝ} (hfix : ∀ i : Fin p, z (Fin.castAdd (m + 1) i) = x i)
    (hzu : z ∘ sidx p m = v) :
    Fin.init z = (Fin.append x (Fin.init v) : Fin (p + m) → ℝ) := by
  funext j
  induction j using Fin.addCases with
  | left i =>
      show z (Fin.castAdd m i).castSucc = Fin.append x (Fin.init v) (Fin.castAdd m i)
      rw [show (Fin.castAdd m i).castSucc = (Fin.castAdd (m + 1) i : Fin (p + m + 1)) from
        Fin.ext (by simp)]
      rw [hfix i, Fin.append_left]
  | right k =>
      show z (Fin.natAdd p k).castSucc = Fin.append x (Fin.init v) (Fin.natAdd p k)
      rw [show (Fin.natAdd p k).castSucc = (Fin.natAdd p k.castSucc : Fin (p + (m + 1))) from
        (Fin.natAdd_castSucc (n := p) (i := k)).symm]
      rw [Fin.append_right]
      have h : z (Fin.natAdd p k.castSucc) = v k.castSucc := congrFun hzu k.castSucc
      rw [h]
      rfl

/-- **The set-theoretic identity of the slicing.**  Fixing the first `p` coordinates of
`graphOf G` to `x` and keeping the trailing `m+1` coordinates (`coordImage` along `sidx`)
gives exactly the graph of the slice `u ↦ G (Fin.append x u)`. -/
theorem coordImage_sidx_eq {p m : ℕ} (G : (Fin (p + m) → ℝ) → ℝ) (x : Fin p → ℝ) :
    Work.WilG5.coordImage (sidx p m)
      (graphOf G ∩ ⋂ i : Fin p, {z : Fin (p + m + 1) → ℝ | z (Fin.castAdd (m + 1) i) = x i})
      = graphOf (fun u : Fin m → ℝ => G (Fin.append x u)) := by
  ext v
  constructor
  · rintro ⟨z, hz, hzu⟩
    rw [Set.mem_inter_iff, Set.mem_iInter] at hz
    obtain ⟨hzG, hzfix⟩ := hz
    have hlast : v (Fin.last m) = z (Fin.last (p + m)) := by
      have h := congrFun hzu (Fin.last m)
      simp only [Function.comp_apply] at h
      rw [← h]
      congr 1
    have hinit := fin_init_eq_append_of hzfix hzu
    change v (Fin.last m) = G (Fin.append x (Fin.init v))
    rw [hlast, ← hinit]
    exact hzG
  · intro hv
    change v (Fin.last m) = G (Fin.append x (Fin.init v)) at hv
    refine ⟨(Fin.append (m := p) (n := m + 1) x v : Fin (p + m + 1) → ℝ), ?_, ?_⟩
    · rw [Set.mem_inter_iff, Set.mem_iInter]
      refine ⟨?_, fun i => Fin.append_left x v i⟩
      have hlast : (Fin.append (m := p) (n := m + 1) x v) (Fin.last (p + m)) = v (Fin.last m) := by
        rw [show Fin.last (p + m) = (Fin.natAdd p (Fin.last m) : Fin (p + (m + 1))) from
          (Fin.natAdd_last (n := p) (m := m)).symm]
        exact Fin.append_right x v (Fin.last m)
      show (Fin.append (m := p) (n := m + 1) x v) (Fin.last (p + m))
        = G (Fin.init ((Fin.append (m := p) (n := m + 1) x v) : Fin (p + m + 1) → ℝ))
      rw [hlast, fin_init_append]
      exact hv
    · funext k
      show (Fin.append (m := p) (n := m + 1) x v) (sidx p m k) = v k
      exact Fin.append_right x v k

/-- **Slicing a `graphOf` at a parameter block.**  If `graphOf G ⊆ ℝ^{p+m+1}` is `Ω`-definable
at format `F` and degree `D`, then the slice `u ↦ G (Fin.append x u)` (the first `p` coordinates
fixed to `x`, the remaining `m+1` kept) is `Ω`-definable at format `F + K` and degree `D + K`
for a constant `K` depending only on `p` and `m`.

Construction: intersect `graphOf G` with the `p` coordinate hyperplanes `{z i = x i}` (each of
degree `1`, so the intersection costs only the *sum* `D + p`), then apply
`Work.WilG5.coordImage_mem` to keep the trailing `m+1` coordinates; the latter adds only
constants to the format and degree. -/
theorem sliceGraph_mem_gen' (S : SOMin) (p m : ℕ) :
    ∃ K : ℕ, ∀ (F D : ℕ) (G : (Fin (p + m) → ℝ) → ℝ) (x : Fin p → ℝ),
      graphOf G ∈ S.Ω F D (p + m + 1) →
      graphOf (fun u : Fin m → ℝ => G (Fin.append x u)) ∈
        S.Ω (F + K) (D + K) (m + 1) := by
  refine ⟨p + m + 3 + 64 * ((p + m + 1) + (m + 1)) + 64, ?_⟩
  intro F D G x hG
  let H : Fin p → Set (Fin (p + m + 1) → ℝ) :=
    fun i => {z : Fin (p + m + 1) → ℝ | z (Fin.castAdd (m + 1) i) = x i}
  have hH : ∀ i : Fin p, H i ∈ S.Ω (p + m + 1) ((Polynomial.C 1).eval D) (p + m + 1) := by
    intro i
    have h1 := coordEqSet_mem_deg1 (S := S) (n := p + m + 1)
      (Fin.castAdd (m + 1) i : Fin (p + m + 1)) (x i)
    simpa [H] using h1
  have hInter0 := Work.WilG1.Omega.inter_mem (S := S) (n := p + m + 1) (k := p)
    (a := p + m + 1) (b := Polynomial.C 1) (D := D) H hH
  have hInter : (⋂ i : Fin p, H i) ∈
      S.Ω ((p + m + 1) + 1) ((Polynomial.C p).eval D) (p + m + 1) := by
    simpa using hInter0
  have hX' : graphOf G ∈ S.Ω (max F ((p + m + 1) + 1))
      ((Polynomial.X : Polynomial ℕ).eval D) (p + m + 1) := by
    have hD : D ≤ ((Polynomial.X : Polynomial ℕ).eval D) := by simp
    exact Work.WilG1.Omega.mono hG (le_max_left _ _) hD
  have hY' : (⋂ i : Fin p, H i) ∈ S.Ω (max F ((p + m + 1) + 1))
      ((Polynomial.C p).eval D) (p + m + 1) :=
    Work.WilG1.Omega.mono hInter (le_max_right _ _) le_rfl
  have hres : (graphOf G ∩ ⋂ i : Fin p, H i) ∈
      S.Ω (max F ((p + m + 1) + 1) + 1)
        (((Polynomial.X : Polynomial ℕ) + Polynomial.C p).eval D) (p + m + 1) := by
    have h := Work.WilG1.Omega.inter₂ (S := S) hX' hY'
    simpa using h
  have hCI := Work.WilG5.coordImage_mem (S := S) (m := m + 1) (N := p + m + 1)
    (ι := sidx p m) hres
  rw [coordImage_sidx_eq G x] at hCI
  refine Work.WilG5.mem_mono hCI (F + (p + m + 3 + 64 * ((p + m + 1) + (m + 1)) + 64))
    (D + (p + m + 3 + 64 * ((p + m + 1) + (m + 1)) + 64)) ?_ ?_
  · have hmax : max F ((p + m + 1) + 1) ≤ F + ((p + m + 1) + 1) := by
      apply max_le <;> omega
    omega
  · simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    omega

/-- A `famGraph` is by definition a `graphOf`, so the flattened family member
`fun z => f (first p coords) (last n+1 coords)` has the same `Ω`-membership as `famGraph f`. -/
theorem famGraph_eq_graphOf_flat (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    WilkiesDesign.CG.famGraph f
      = graphOf (fun z : Fin (p + (n + 1)) → ℝ =>
          f (fun i => z (Fin.castAdd (n + 1) i)) (fun j => z (Fin.natAdd p j))) := rfl

/-- The graph of a member `f l` of an `Ω`-definable family of `(n+1)`-variable functions over the
parameter space `Fin p → ℝ` is itself `Ω`-bounded, uniformly in the parameter value `l` (the
parameter coordinates are fixed by the polynomial sets `{z | z (castAdd i) = l i}` and then
projected away). -/
theorem graphOf_member_mem (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ K : ℕ, ∀ (F D : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (l : Fin p → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F D (p + (n + 1) + 1) →
      WilkiesDesign.graphOf (f l) ∈ S.Ω (F + K) (D + K) (n + 1 + 1) := by
  obtain ⟨K, hK⟩ := sliceGraph_mem_gen' S p (n + 1)
  refine ⟨K, ?_⟩
  intro F D f l hf
  have hf' : graphOf (fun z : Fin (p + (n + 1)) → ℝ =>
      f (fun i => z (Fin.castAdd (n + 1) i)) (fun j => z (Fin.natAdd p j))) ∈
      S.Ω F D (p + (n + 1) + 1) := by
    rw [← famGraph_eq_graphOf_flat p n f]; exact hf
  have h := hK F D (fun z : Fin (p + (n + 1)) → ℝ =>
      f (fun i => z (Fin.castAdd (n + 1) i)) (fun j => z (Fin.natAdd p j))) l hf'
  have hfun : (fun u : Fin (n + 1) → ℝ =>
      (fun z : Fin (p + (n + 1)) → ℝ => f (fun i => z (Fin.castAdd (n + 1) i))
        (fun j => z (Fin.natAdd p j))) (Fin.append l u)) = f l := by
    funext u
    show f (fun i => Fin.append l u (Fin.castAdd (n + 1) i))
        (fun j => Fin.append l u (Fin.natAdd p j)) = f l u
    congr 1
    · funext i; rw [Fin.append_left]
    · funext j; rw [Fin.append_right]
  rw [hfun] at h
  exact h

end Work.WilG4c
