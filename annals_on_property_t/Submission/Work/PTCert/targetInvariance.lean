import Mathlib
import Submission.Work.PTCert.Interfaces
import Submission.Work.RouteB.EdgeLap
import Submission.Work.PTCert.sigAutConj_mem_SAutGen
import Submission.Work.PTCert.sigAutConjSEdge

/-!
# Invariance of the certificate targets under conjugation by signed permutations

`TargetInvariance r` (see `Submission/Work/PTCert/Interfaces.lean`) says that for every
signed permutation `g ∈ SigmaSet r` the three elements `deltaSub r r`, `AdjPair r r`,
`OpPair r r` of `ℝ[Aut(F_r)]` are fixed by conjugation by `of g`:

`of g * X * of g⁻¹ = X`.

The proof has two inputs, proved separately in
`Submission/Work/PTCert/sigAutConjSEdge.lean` and
`Submission/Work/PTCert/sigAutConj_mem_SAutGen.lean`:

* conjugation by `sigAut p s` maps the transvection set `SEdge e` of an edge onto
  `SEdge (p • e)`;
* conjugation by `sigAut p s` preserves the Nielsen transvection set `SAutGen r`.

The remaining content is bookkeeping: conjugation of a Laplacian
(`conj_laplacian_image`), expansion of the conjugation over products and sums
(`conj_mul_expand`, `Finset.mul_sum`/`Finset.sum_mul`), and the fact that the pair
sets `Psub r r`/`Qsub r r` are stable under the diagonal action of `p` on pairs of
edges (`sum_pair_smul_eq`).
-/

namespace Work.PTCert

open OnPropertyT Submission.FreeGroupAut Submission.RouteB Submission.RouteB.Edge Submission.PTCert
open scoped BigOperators

set_option autoImplicit false

variable {r : ℕ}

/-! ## Conjugation of Laplacians, products and sums -/

/-- The two ways of writing the conjugation map of a group on itself. -/
lemma image_conj_eq (γ : MulAut (FreeGroup (Fin r)))
    (S : Finset (MulAut (FreeGroup (Fin r)))) :
    S.image (fun x => γ * x * γ⁻¹) = S.image (MulAut.conj γ) := by
  have hf : (fun x => γ * x * γ⁻¹) = ⇑(MulAut.conj γ) := by
    funext x; rw [MulAut.conj_apply]
  rw [hf]

/-- Conjugating a Laplacian: if the conjugates of the elements of `S` are exactly the
elements of `T`, then `of γ * Laplacian S * of γ⁻¹ = Laplacian T`. -/
lemma conj_laplacian_image (γ : MulAut (FreeGroup (Fin r)))
    {S T : Finset (MulAut (FreeGroup (Fin r)))}
    (h : S.image (fun x => γ * x * γ⁻¹) = T) :
    MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) γ * OnPropertyT.Laplacian S
      * MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) γ⁻¹ = OnPropertyT.Laplacian T := by
  change MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) γ
      * Commons.Algebra.MonoidAlgebra.Laplacian S
      * MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) γ⁻¹
    = Commons.Algebra.MonoidAlgebra.Laplacian T
  rw [Commons.Algebra.MonoidAlgebra.conj_laplacian, h]

/-- Conjugation distributes over products in the group ring. -/
lemma conj_mul_expand (γ : MulAut (FreeGroup (Fin r)))
    (x y : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r)))) :
    MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) γ * (x * y)
        * MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) γ⁻¹
      = (MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) γ * x
          * MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) γ⁻¹)
        * (MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) γ * y
          * MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) γ⁻¹) := by
  rw [Commons.Algebra.MonoidAlgebra.of_conj_mul_of, map_mul,
      ← Commons.Algebra.MonoidAlgebra.of_conj_mul_of x γ,
      ← Commons.Algebra.MonoidAlgebra.of_conj_mul_of y γ]

/-! ## Conjugation of the edge Laplacians -/

/-- Conjugation of the Laplacian `edgeLap e` of an edge, transported along the
permutation of the edges induced by `sigAut p s`. -/
lemma edgeLap_conj (p : Equiv.Perm (Fin r)) (s : Fin r → Bool) (e : Edge r)
    (h : (SEdge e).image (MulAut.conj (sigAut p s)) = SEdge (p • e)) :
    MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (sigAut p s) * edgeLap e
        * MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (sigAut p s)⁻¹
      = edgeLap (p • e) := by
  have h' : (SEdge e).image (fun x => sigAut p s * x * (sigAut p s)⁻¹) = SEdge (p • e) := by
    rw [image_conj_eq]; exact h
  rw [show edgeLap e = OnPropertyT.Laplacian (SEdge e) from rfl,
      show edgeLap (p • e) = OnPropertyT.Laplacian (SEdge (p • e)) from rfl,
      conj_laplacian_image (sigAut p s) h']

/-- Conjugation of `deltaSub r r = Laplacian (SAutGen r)`, from preservation of the
Nielsen transvection set. -/
lemma deltaSub_conj (p : Equiv.Perm (Fin r)) (s : Fin r → Bool)
    (h : ∀ x ∈ SAutGen r, sigAut p s * x * (sigAut p s)⁻¹ ∈ SAutGen r) :
    MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (sigAut p s) * deltaSub r r
        * MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (sigAut p s)⁻¹ = deltaSub r r := by
  have hmem : (SAutGen r).image (fun x => sigAut p s * x * (sigAut p s)⁻¹) = SAutGen r := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact h x hx
    · rw [Finset.card_image_of_injOn (s := SAutGen r)
        (f := fun x => sigAut p s * x * (sigAut p s)⁻¹)]
      exact fun a _ b _ hab => mul_left_cancel (mul_right_cancel hab)
  rw [deltaSub_top]
  exact conj_laplacian_image (sigAut p s) hmem

/-! ## Reindexing the sums over pairs of edges -/

/-- Reindexing a sum over a set of pairs of edges stable under the diagonal action of
`p`. -/
lemma sum_pair_smul_eq {M : Type*} [AddCommMonoid M] (p : Equiv.Perm (Fin r))
    (S : Finset (Edge r × Edge r)) (φ : Edge r × Edge r → M)
    (hsta : ∀ x ∈ S, (p • x.1, p • x.2) ∈ S) :
    ∑ x ∈ S, φ (p • x.1, p • x.2) = ∑ x ∈ S, φ x := by
  classical
  have hinj : Set.InjOn (fun x : Edge r × Edge r => (p • x.1, p • x.2)) ↑S := by
    intro a _ b _ hab
    have h1 : p • a.1 = p • b.1 := congrArg Prod.fst hab
    have h2 : p • a.2 = p • b.2 := congrArg Prod.snd hab
    rw [smul_eq_iff] at h1 h2
    exact Prod.ext h1 h2
  have him : S.image (fun x : Edge r × Edge r => (p • x.1, p • x.2)) = S := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact hsta x hx
    · exact le_of_eq (Finset.card_image_of_injOn hinj).symm
  rw [← Finset.sum_image (f := φ) (g := fun x : Edge r × Edge r => (p • x.1, p • x.2)) hinj,
    him]

/-- `Psub r r` (adjacent ordered pairs of edges) is stable under the diagonal action. -/
lemma mem_Psub_smul (p : Equiv.Perm (Fin r)) {x : Edge r × Edge r} (hx : x ∈ Psub r r) :
    (p • x.1, p • x.2) ∈ Psub r r := by
  rw [mem_Psub] at hx ⊢
  exact ⟨(smul_adj p x.1 x.2).mpr hx.1, by rw [Esub_self]; exact Finset.mem_univ _,
    by rw [Esub_self]; exact Finset.mem_univ _⟩

/-- `Qsub r r` (opposite ordered pairs of edges) is stable under the diagonal action. -/
lemma mem_Qsub_smul (p : Equiv.Perm (Fin r)) {x : Edge r × Edge r} (hx : x ∈ Qsub r r) :
    (p • x.1, p • x.2) ∈ Qsub r r := by
  rw [mem_Qsub] at hx ⊢
  exact ⟨(smul_op p x.1 x.2).mpr hx.1, by rw [Esub_self]; exact Finset.mem_univ _,
    by rw [Esub_self]; exact Finset.mem_univ _⟩

/-- Conjugation of a sum of products `∑_{(e,f) ∈ S} φ e * φ f` over a set of pairs of
edges stable under `p`, where `φ` is equivariant with the edge permutation. -/
lemma Pair_conj (p : Equiv.Perm (Fin r)) (s : Fin r → Bool) (S : Finset (Edge r × Edge r))
    (φ : Edge r → MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))))
    (hφ : ∀ e, MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (sigAut p s) * φ e
        * MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (sigAut p s)⁻¹ = φ (p • e))
    (hsta : ∀ x ∈ S, (p • x.1, p • x.2) ∈ S) :
    MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (sigAut p s) * (∑ x ∈ S, φ x.1 * φ x.2)
        * MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (sigAut p s)⁻¹
      = ∑ x ∈ S, φ x.1 * φ x.2 := by
  rw [Finset.mul_sum, Finset.sum_mul]
  trans ∑ x ∈ S, φ (p • x.1) * φ (p • x.2)
  · refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [conj_mul_expand (sigAut p s) (φ x.1) (φ x.2), hφ x.1, hφ x.2]
  · exact sum_pair_smul_eq p S (fun y => φ y.1 * φ y.2) hsta

/-! ## Assembly -/

/-- `TargetInvariance r` follows from the invariance of the edge transvection sets
(the `sorry`-free input `sigAutConjSEdge`); preservation of the Nielsen transvection
set `SAutGen r` is `Work.PTCert.sigAutConj_mem_SAutGen`. -/
theorem targetInvariance_of (r : ℕ)
    (hA : ∀ (p : Equiv.Perm (Fin r)) (s : Fin r → Bool) (e : Edge r),
      (SEdge e).image (MulAut.conj (sigAut p s)) = SEdge (p • e)) :
    TargetInvariance r := by
  intro g hg
  have hg' : g ∈ Submission.PTCert.SigmaSet r := hg
  rw [Submission.PTCert.SigmaSet] at hg'
  obtain ⟨⟨p, s⟩, -, hgs⟩ := Finset.mem_image.mp hg'
  subst hgs
  refine ⟨?_, ?_, ?_⟩
  · exact deltaSub_conj p s (fun x hx => sigAutConj_mem_SAutGen r p s hx)
  · rw [show AdjPair r r = ∑ x ∈ Psub r r, edgeLap x.1 * edgeLap x.2 from rfl]
    exact Pair_conj p s (Psub r r) edgeLap (fun e => edgeLap_conj p s e (hA p s e))
      (fun x hx => mem_Psub_smul p hx)
  · rw [show OpPair r r = ∑ x ∈ Qsub r r, edgeLap x.1 * edgeLap x.2 from rfl]
    exact Pair_conj p s (Qsub r r) edgeLap (fun e => edgeLap_conj p s e (hA p s e))
      (fun x hx => mem_Qsub_smul p hx)

/-- **(T2) Invariance of the targets** under conjugation by signed permutations. -/
theorem targetInvariance (r : ℕ) : TargetInvariance r :=
  targetInvariance_of r (fun p s e => sigAutConjSEdge r p s e)

end Work.PTCert
