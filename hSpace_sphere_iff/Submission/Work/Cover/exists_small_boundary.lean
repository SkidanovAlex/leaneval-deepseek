import Mathlib
import Submission.Work.Cohomology.Cover
import Submission.Work.Cohomology.sdFun_chainMap
import Submission.Work.Cohomology.tFun_homotopy
import Submission.Work.Cohomology.H_equiv_dual_annihilator
import Submission.Work.Cover.chainIn_sdFun_pow_of_cover
import Submission.Work.Cover.sdFun_mem_chainIn
import Submission.Work.Cover.tFun_mem_chainIn

open CategoryTheory Simplicial Opposite

namespace Work.Cover

noncomputable section

/-! ## The subdivision and the prism preserve the chains in a two-set cover

`chainIn X W m` is the submodule of `m`-chains of `X` spanned by the simplices whose image lies
in `W`.  For an open cover `X = U ∪ V` the submodule of *small* chains is
`chainIn X U m ⊔ chainIn X V m`.  Since `sdFun` and `tFun` push the subdivision/prism of `Δ^m`
forward along the simplex, and the whole of `Δ^m` is mapped into any set containing the image of
the simplex, both operators preserve the small chains (`sdFun_mem_chainIn`,
`tFun_mem_chainIn`); being linear, they preserve the *sum* of the two pieces. -/

lemma sdFun_mem_sup (X : TopCat.{0}) (U V : Set X) (m : ℕ)
    {c : Submission.Cohomology.SChain (TopCat.toSSet.obj X) ℚ m}
    (hc : c ∈ Submission.Cohomology.chainIn X U m ⊔ Submission.Cohomology.chainIn X V m) :
    Submission.Cohomology.sdFun X m c
      ∈ Submission.Cohomology.chainIn X U m ⊔ Submission.Cohomology.chainIn X V m := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hc
  rw [map_add, Submodule.mem_sup]
  exact ⟨_, Work.Cover.sdFun_mem_chainIn X U m (Submodule.mem_map_of_mem ha),
    _, Work.Cover.sdFun_mem_chainIn X V m (Submodule.mem_map_of_mem hb), rfl⟩

lemma tFun_mem_sup (X : TopCat.{0}) (U V : Set X) (m : ℕ)
    {c : Submission.Cohomology.SChain (TopCat.toSSet.obj X) ℚ m}
    (hc : c ∈ Submission.Cohomology.chainIn X U m ⊔ Submission.Cohomology.chainIn X V m) :
    Submission.Cohomology.tFun X m c
      ∈ Submission.Cohomology.chainIn X U (m+1) ⊔ Submission.Cohomology.chainIn X V (m+1) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hc
  rw [map_add, Submodule.mem_sup]
  exact ⟨_, Work.Cover.tFun_mem_chainIn X U m (Submodule.mem_map_of_mem ha),
    _, Work.Cover.tFun_mem_chainIn X V m (Submodule.mem_map_of_mem hb), rfl⟩

section IterateAux

/-- The iterate of an additive map is additive. -/
lemma iterate_lm_add {M : Type*} [AddCommMonoid M] [Module ℚ M] (f : M →ₗ[ℚ] M) (N : ℕ)
    (x y : M) : f^[N] (x + y) = f^[N] x + f^[N] y := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, map_add]

/-- The iterate of an additive map commutes with subtraction. -/
lemma iterate_lm_sub {M : Type*} [AddCommGroup M] [Module ℚ M] (f : M →ₗ[ℚ] M) (N : ℕ)
    (x y : M) : f^[N] (x - y) = f^[N] x - f^[N] y := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, map_sub]

/-- The iterate of a linear map commutes with scalar multiplication. -/
lemma iterate_lm_smul {M : Type*} [AddCommMonoid M] [Module ℚ M] (f : M →ₗ[ℚ] M) (N : ℕ)
    (r : ℚ) (x : M) : f^[N] (r • x) = r • f^[N] x := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, map_smul]

/-- Splitting an iterate at an intermediate time. -/
lemma iterate_max_sub_left {α : Type*} (f : α → α) (a b : ℕ) (x : α) :
    f^[max a b] x = f^[max a b - a] (f^[a] x) := by
  have h := Function.iterate_add_apply f (max a b - a) a x
  rw [Nat.sub_add_cancel (le_max_left a b)] at h
  exact h

/-- Splitting an iterate at an intermediate time (the other factor). -/
lemma iterate_max_sub_right {α : Type*} (f : α → α) (a b : ℕ) (x : α) :
    f^[max a b] x = f^[max a b - b] (f^[b] x) := by
  have h := Function.iterate_add_apply f (max a b - b) b x
  rw [Nat.sub_add_cancel (le_max_right a b)] at h
  exact h

end IterateAux

lemma iterate_sdFun_mem_sup (X : TopCat.{0}) (U V : Set X) (m : ℕ)
    {c : Submission.Cohomology.SChain (TopCat.toSSet.obj X) ℚ m}
    (hc : c ∈ Submission.Cohomology.chainIn X U m ⊔ Submission.Cohomology.chainIn X V m)
    (j : ℕ) :
    (Submission.Cohomology.sdFun X m)^[j] c
      ∈ Submission.Cohomology.chainIn X U m ⊔ Submission.Cohomology.chainIn X V m := by
  induction j with
  | zero => simpa using hc
  | succ j ih => rw [Function.iterate_succ_apply']; exact sdFun_mem_sup X U V m ih

/-- **Every chain becomes small after enough subdivisions.**  For a cover `X = U ∪ V` by open
sets and any `m`-chain `c`, some iterate of the barycentric subdivision lies in the small chains
`chainIn X U m ⊔ chainIn X V m`.  The point is the Lebesgue number lemma
(`chainIn_sdFun_pow_of_cover`), which gives the statement for a single simplex; linearity and the
fact that `sdFun` preserves the small chains propagate it to arbitrary chains. -/
lemma exists_iterate_sdFun_mem_sup (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (hUV : ∀ x, x ∈ U ∨ x ∈ V) (m : ℕ)
    (c : Submission.Cohomology.SChain (TopCat.toSSet.obj X) ℚ m) :
    ∃ N : ℕ, (Submission.Cohomology.sdFun X m)^[N] c
      ∈ Submission.Cohomology.chainIn X U m ⊔ Submission.Cohomology.chainIn X V m := by
  induction c using Finsupp.induction_linear with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add x y hx hy =>
      obtain ⟨Nx, hxN⟩ := hx
      obtain ⟨Ny, hyN⟩ := hy
      refine ⟨max Nx Ny, ?_⟩
      rw [iterate_lm_add]
      refine Submodule.add_mem _ ?_ ?_
      · rw [iterate_max_sub_left]
        exact iterate_sdFun_mem_sup X U V m hxN _
      · rw [iterate_max_sub_right]
        exact iterate_sdFun_mem_sup X U V m hyN _
  | single σ r =>
      obtain ⟨N, hN⟩ := Work.Cover.chainIn_sdFun_pow_of_cover X U V hU hV hUV m σ
      refine ⟨N, ?_⟩
      have hs : (Finsupp.single σ r : Submission.Cohomology.SChain (TopCat.toSSet.obj X) ℚ m)
          = r • Finsupp.single σ (1 : ℚ) := by
        rw [Finsupp.smul_single]; simp
      rw [hs, iterate_lm_smul]
      exact Submodule.smul_mem _ r hN

/-! ## The subdivision is the identity in degree zero -/

lemma sdFun_zero (X : TopCat.{0})
    (c : Submission.Cohomology.SChain (TopCat.toSSet.obj X) ℚ 0) :
    Submission.Cohomology.sdFun X 0 c = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy]
  | single σ r =>
      rw [Submission.Cohomology.sdFun_single]
      have hsd : Submission.Cohomology.sdUniv 0
          = Finsupp.single (Submission.Cohomology.simplexOfPiece
              (Submission.Cohomology.idPiece 0)) 1 := by
        simp only [Submission.Cohomology.sdUniv, Submission.Cohomology.SdPieces]
        rw [Submission.Cohomology.toSingChain_single, one_smul]
      rw [hsd, Submission.Cohomology.pushChain_single,
        Submission.Cohomology.pushSimplex_homOfSimplex_idPiece, Finsupp.smul_single]
      simp

lemma iterate_sdFun_zero (X : TopCat.{0}) (N : ℕ)
    (c : Submission.Cohomology.SChain (TopCat.toSSet.obj X) ℚ 0) :
    (Submission.Cohomology.sdFun X 0)^[N] c = c := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply']; rw [ih]; exact sdFun_zero X c

/-! ## The iteration of the subdivision as a chain map -/

lemma iterate_sdFun_sbdry (X : TopCat.{0}) (m N : ℕ)
    (z : Submission.Cohomology.SChain (TopCat.toSSet.obj X) ℚ (m+1)) :
    Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ m
        ((Submission.Cohomology.sdFun X (m+1))^[N] z)
      = (Submission.Cohomology.sdFun X m)^[N]
          (Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ m z) := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Function.iterate_succ_apply']
      rw [← Work.Cohomology.sdFun_chainMap, ih]

/-! ## The partial chain homotopy from the iterated subdivision to the identity

`dFun X N m : C_m → C_{m+1}` is the sum of the partial homotopies `Sd^j ∘ T`, `j < N`; it
realises the chain homotopy `∂ D + D ∂ = id - Sd^N`.  The identity actually used below is the
degree-`m` instance of this relation, where the second term `D ∂` can be dropped because the
chain is a cycle. -/

/-- The `N`-term partial chain homotopy from the `N`-fold barycentric subdivision to the
identity, in degree `m`. -/
def dFun (X : TopCat.{0}) (N m : ℕ) :
    Submission.Cohomology.SChain (TopCat.toSSet.obj X) ℚ m →ₗ[ℚ]
      Submission.Cohomology.SChain (TopCat.toSSet.obj X) ℚ (m+1) :=
  ∑ j ∈ Finset.range N,
    ((Submission.Cohomology.sdFun X (m+1)) ^ j).comp (Submission.Cohomology.tFun X m)

lemma dFun_succ (X : TopCat.{0}) (N m : ℕ) :
    dFun X (N+1) m
      = dFun X N m + ((Submission.Cohomology.sdFun X (m+1)) ^ N).comp
          (Submission.Cohomology.tFun X m) := by
  simp only [dFun, Finset.sum_range_succ]

lemma dFun_mem_sup (X : TopCat.{0}) (U V : Set X) (k N : ℕ)
    {c : Submission.Cohomology.SChain (TopCat.toSSet.obj X) ℚ (k+1)}
    (hc : c ∈ Submission.Cohomology.chainIn X U (k+1) ⊔ Submission.Cohomology.chainIn X V (k+1)) :
    dFun X N (k+1) c
      ∈ Submission.Cohomology.chainIn X U (k+2) ⊔ Submission.Cohomology.chainIn X V (k+2) := by
  rw [dFun, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [LinearMap.comp_apply, Module.End.pow_apply]
  exact iterate_sdFun_mem_sup X U V (k+2) (tFun_mem_sup X U V (k+1) hc) j

/-- **The fundamental identity of the partial homotopy.**  For `c ∈ C_{k+1}` the boundary of
`D c ∈ C_{k+2}` is `c - Sd^N c - D (∂c)`; for a cycle `c` the last term vanishes and
`∂(D c) = c - Sd^N c`, which is what makes the small boundary of a small cycle small. -/
lemma sbdry_dFun (X : TopCat.{0}) (N : ℕ) :
    ∀ (k : ℕ) (c : Submission.Cohomology.SChain (TopCat.toSSet.obj X) ℚ (k+1)),
      Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ (k+1) (dFun X N (k+1) c)
        = c - (Submission.Cohomology.sdFun X (k+1))^[N] c
          - dFun X N k (Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ k c) := by
  induction N with
  | zero =>
      intro k c
      simp only [dFun, Finset.range_zero, Finset.sum_empty, LinearMap.zero_apply,
        Function.iterate_zero, id_eq, map_zero, sub_zero]
      simp
  | succ M ih =>
      intro k c
      have hD : dFun X (M+1) (k+1) c
          = dFun X M (k+1) c + (Submission.Cohomology.sdFun X (k+2))^[M]
              (Submission.Cohomology.tFun X (k+1) c) := by
        rw [dFun_succ, LinearMap.add_apply, LinearMap.comp_apply, Module.End.pow_apply]
      have hDk : dFun X (M+1) k (Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ k c)
          = dFun X M k (Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ k c)
            + (Submission.Cohomology.sdFun X (k+1))^[M]
                (Submission.Cohomology.tFun X k
                  (Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ k c)) := by
        rw [dFun_succ, LinearMap.add_apply, LinearMap.comp_apply, Module.End.pow_apply]
      have hT : Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ (k+1)
            (Submission.Cohomology.tFun X (k+1) c)
          = c - Submission.Cohomology.sdFun X (k+1) c
            - Submission.Cohomology.tFun X k
                (Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ k c) := by
        rw [← Work.Cohomology.tFun_homotopy X k c]; abel
      rw [hD, hDk, map_add, ih k c, iterate_sdFun_sbdry, hT, iterate_lm_sub, iterate_lm_sub,
        Function.iterate_succ_apply]
      abel

/-! ## The small-boundary lemma -/

theorem exists_small_boundary (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (hUV : ∀ x, x ∈ U ∨ x ∈ V) (n : ℕ)
    (c : Submission.Cohomology.SChain (TopCat.toSSet.obj X) ℚ n)
    (hc : c ∈ Submission.Cohomology.chainIn X U n ⊔ Submission.Cohomology.chainIn X V n)
    (hb : c ∈ Submission.Cohomology.chainBoundaries (TopCat.toSSet.obj X) ℚ n) :
    ∃ d ∈ Submission.Cohomology.chainIn X U (n+1) ⊔ Submission.Cohomology.chainIn X V (n+1),
      Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ n d = c := by
  rcases n with _ | k
  · obtain ⟨y, hy⟩ := Submission.Cohomology.mem_chainBoundaries.mp hb
    obtain ⟨N, hN⟩ := exists_iterate_sdFun_mem_sup X U V hU hV hUV (0+1) y
    refine ⟨(Submission.Cohomology.sdFun X (0+1))^[N] y, hN, ?_⟩
    rw [iterate_sdFun_sbdry, hy, iterate_sdFun_zero]
  · obtain ⟨y, hy⟩ := Submission.Cohomology.mem_chainBoundaries.mp hb
    obtain ⟨N, hN⟩ := exists_iterate_sdFun_mem_sup X U V hU hV hUV (k+1+1) y
    refine ⟨(Submission.Cohomology.sdFun X (k+1+1))^[N] y + dFun X N (k+1) c, ?_, ?_⟩
    · exact Submodule.add_mem _ hN (dFun_mem_sup X U V k N hc)
    · have hcyc : Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ k c = 0 := by
        rw [← hy]
        exact Work.Cohomology.sbdry_sbdry_eq_zero (TopCat.toSSet.obj X) k y
      rw [map_add, iterate_sdFun_sbdry, hy, sbdry_dFun, hcyc, map_zero]
      abel

end

end Work.Cover
