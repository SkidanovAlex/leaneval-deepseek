import Mathlib
import Submission.Work.Higman.cob_facts
import Submission.Work.Higman.fin_sum_split

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

open scoped BigOperators

/-- The candidate coboundary attached to a choice of basis `B` of a finite `𝔽₂`-vector space `V`
and a biadditive form `c : V → V → W`:

  `f v = ∑_{i < j} c (aᵢ • eᵢ) (aⱼ • eⱼ)`,  where `aᵢ = B.equivFun v i` and `eᵢ = B i`.

This is the quadratic refinement of `c`; the fact that its polar form is `c` (i.e. that it is a
coboundary) is `Work.Higman.exists_additive_coboundary`.  Note that the coefficients `aᵢ ∈ ZMod 2`
are placed *inside* `c`, as scalar multiples of basis vectors in `V`, so that no scalar action of
`ZMod 2` on the merely-additive group `W` is needed (there is none, in general). -/
noncomputable def coboundaryOfBasis {V W : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] {n : ℕ} (B : Module.Basis (Fin n) (ZMod 2) V) (c : V → V → W) (v : V) : W :=
  ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2),
    c ((B.equivFun v p.1) • B p.1) ((B.equivFun v p.2) • B p.2)

/-- Every alternating `𝔽₂`-biadditive form on a finite `𝔽₂`-vector space is a coboundary.
(Choose a basis `e_i`; put `f (∑ a_i e_i) = ∑_{i<j} a_i a_j c e_i e_j`.) -/
theorem exists_additive_coboundary
    {V W : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [AddCommGroup W] (c : V → V → W)
    (hc1 : ∀ a b d : V, c (a + b) d = c a d + c b d)
    (hc2 : ∀ a b d : V, c a (b + d) = c a b + c a d)
    (halt : ∀ a : V, c a a = 0) :
    ∃ f : V → W, ∀ a b : V, f (a + b) + (f a + f b) = c a b := by
  classical
  obtain ⟨h0y, hx0, hskew, htwo, hsmul, hexp⟩ := cob_facts c hc1 hc2 halt
  -- a finite-dimensional `𝔽₂`-vector space, with a chosen basis
  let n := Module.finrank (ZMod 2) V
  let B : Module.Basis (Fin n) (ZMod 2) V := Module.finBasis (ZMod 2) V
  -- `F` indexes the pairs `i < j` of basis vectors
  let F : Finset (Fin n × Fin n) := (Finset.univ).filter (fun p => p.1 < p.2)
  -- `c` is additive in each variable, hence linear over finitely many summands
  have hsum_left : ∀ (f : Fin n → V) (y : V), c (∑ i, f i) y = ∑ i, c (f i) y := fun f y =>
    map_sum (AddMonoidHom.mk' (fun x => c x y) (fun p q => hc1 p q y)) f Finset.univ
  have hsum_right : ∀ (x : V) (g : Fin n → V), c x (∑ i, g i) = ∑ i, c x (g i) := fun x g =>
    map_sum (AddMonoidHom.mk' (fun y => c x y) (fun p q => hc2 x p q)) g Finset.univ
  refine ⟨coboundaryOfBasis B c, ?_⟩
  intro a b
  -- the coordinate pieces `Pa i = aᵢ • eᵢ` (with `a = ∑ i, Pa i`) and likewise `Pb`
  let Pa : Fin n → V := fun i => (B.equivFun a i) • B i
  let Pb : Fin n → V := fun i => (B.equivFun b i) • B i
  set U : W := ∑ p ∈ F, c (Pa p.1) (Pb p.2) with hUdef
  set Vv : W := ∑ p ∈ F, c (Pb p.1) (Pa p.2) with hVdef
  set D : W := ∑ i, c (Pa i) (Pb i) with hDdef
  set L : W := ∑ p ∈ F, c (Pa p.2) (Pb p.1) with hLdef
  set T : W := ∑ i, ∑ j, c (Pa i) (Pb j) with hTdef
  -- folding of the three sums `f (a+b) + f a + f b` into one sum
  have hSa : coboundaryOfBasis B c a = ∑ p ∈ F, c (Pa p.1) (Pa p.2) := by
    simp only [coboundaryOfBasis, F, Pa]
  have hSb : coboundaryOfBasis B c b = ∑ p ∈ F, c (Pb p.1) (Pb p.2) := by
    simp only [coboundaryOfBasis, F, Pb]
  have hSab : coboundaryOfBasis B c (a + b)
      = ∑ p ∈ F, c (Pa p.1 + Pb p.1) (Pa p.2 + Pb p.2) := by
    simp only [coboundaryOfBasis, F, Pa, Pb, map_add, Pi.add_apply, add_smul]
  have hcomb : (∑ p ∈ F, (c (Pa p.1 + Pb p.1) (Pa p.2 + Pb p.2)
        + (c (Pa p.1) (Pa p.2) + c (Pb p.1) (Pb p.2))))
      = coboundaryOfBasis B c (a + b)
        + (coboundaryOfBasis B c a + coboundaryOfBasis B c b) := by
    rw [hSab, hSa, hSb, Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- the expansion of `f (a+b) + f a + f b`: termwise `hexp` kills the doubled terms
  have hL : coboundaryOfBasis B c (a + b)
      + (coboundaryOfBasis B c a + coboundaryOfBasis B c b) = U + Vv := by
    rw [← hcomb, hUdef, hVdef, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [← add_assoc, hexp]
  -- the double sum is the biadditive form evaluated at `(a, b)`
  have hT : T = c a b := by
    rw [hTdef]
    have hsa : (∑ i, Pa i) = a := by
      simp only [Pa]; exact Module.Basis.sum_equivFun B a
    have hsb : (∑ i, Pb i) = b := by
      simp only [Pb]; exact Module.Basis.sum_equivFun B b
    rw [← hsa, ← hsb, hsum_left]
    simp only [hsum_right]
  -- triangular decomposition of the double sum
  have h_split : T = U + D + L := by
    rw [hTdef, hUdef, hDdef, hLdef]
    exact fin_sum_split n (fun i j => c (Pa i) (Pb j))
  -- the diagonal term vanishes
  have hD : D = 0 := by
    rw [hDdef]
    exact Finset.sum_eq_zero (fun i _ => by simp only [Pa, Pb]; exact hsmul _ _ _)
  -- the lower triangle is the negative of `Vv`
  have hLneg : L = -Vv := by
    rw [hLdef, hVdef, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun p _ => hskew (Pb p.1) (Pa p.2))
  -- `Vv` is `2`-torsion, hence equal to its own negative
  have h2V : Vv + Vv = 0 := by
    rw [hVdef, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun p _ => htwo _ _)
  have hVeq : Vv = -Vv := by rw [eq_neg_iff_add_eq_zero]; exact h2V
  have hVL : Vv = L := hVeq.trans hLneg.symm
  calc coboundaryOfBasis B c (a + b)
        + (coboundaryOfBasis B c a + coboundaryOfBasis B c b)
      = U + Vv := hL
    _ = U + L := by rw [hVL]
    _ = U + D + L := by rw [hD, add_zero]
    _ = T := h_split.symm
    _ = c a b := hT

end Work.Higman
