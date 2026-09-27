import Mathlib
import Submission.Work.Cohomology.Basic
import Submission.Work.Cohomology.Cup
import Submission.Work.Cohomology.coboundary_comp
import Submission.Work.Cohomology.cupOf_coboundary
import Submission.Work.Cohomology.Cohomology
import Submission.Work.Cohomology.prism_sum

open CategoryTheory Simplicial Opposite
open scoped BigOperators
open Submission.Cohomology

namespace Work.Cohomology

variable {S T : SSet.{0}} {R : Type} [CommRing R] {f g : S ⟶ T}

/-- The underlying function of the `i`-th component of a simplicial homotopy, in degree `m`:
`h_i : S _⦋m⦌ → T _⦋m+1⦌` for `i : Fin (m+1)`. -/
noncomputable def hfun (H : SSet.Homotopy f g) (m : ℕ) (i : Fin (m+1)) :
    S _⦋m⦌ → T _⦋m+1⦌ :=
  fun x => (H.toSimplicialObjectHomotopy.h i) x

lemma hfun_zero (H : SSet.Homotopy f g) (m : ℕ) (σ : S _⦋m⦌) :
    T.δ (0 : Fin (m+2)) (hfun H m 0 σ) = g.app (op ⦋m⦌) σ := by
  have h2 := ConcreteCategory.congr_hom (H.toSimplicialObjectHomotopy.h_zero_comp_δ_zero m) σ
  simpa only [hfun, CategoryTheory.comp_apply] using h2

lemma hfun_last (H : SSet.Homotopy f g) (m : ℕ) (σ : S _⦋m⦌) :
    T.δ (Fin.last (m+1)) (hfun H m (Fin.last m) σ) = f.app (op ⦋m⦌) σ := by
  have h2 := ConcreteCategory.congr_hom (H.toSimplicialObjectHomotopy.h_last_comp_δ_last m) σ
  simpa only [hfun, CategoryTheory.comp_apply] using h2

lemma hfun_succ_δ (H : SSet.Homotopy f g) {m : ℕ} (i : Fin (m+2)) (j : Fin (m+1))
    (hij : i ≤ j.castSucc) (τ : S _⦋m+1⦌) :
    T.δ i.castSucc (hfun H (m+1) j.succ τ) = hfun H m j (S.δ i τ) := by
  have h2 := ConcreteCategory.congr_hom
    (H.toSimplicialObjectHomotopy.h_succ_comp_δ_castSucc_of_lt i j hij) τ
  simpa only [hfun, CategoryTheory.comp_apply] using h2

lemma hfun_castSucc_δ (H : SSet.Homotopy f g) {m : ℕ} (i : Fin (m+2)) (j : Fin (m+1))
    (hij : j.castSucc < i) (τ : S _⦋m+1⦌) :
    T.δ i.succ (hfun H (m+1) j.castSucc τ) = hfun H m j (S.δ i τ) := by
  have h2 := ConcreteCategory.congr_hom
    (H.toSimplicialObjectHomotopy.h_castSucc_comp_δ_succ_of_lt i j hij) τ
  simpa only [hfun, CategoryTheory.comp_apply] using h2

lemma hfun_mid (H : SSet.Homotopy f g) {m : ℕ} (j : Fin (m+1)) (τ : S _⦋m+1⦌) :
    T.δ j.castSucc.succ (hfun H (m+1) j.succ τ)
      = T.δ j.castSucc.succ (hfun H (m+1) j.castSucc τ) := by
  have h2 := ConcreteCategory.congr_hom
    (H.toSimplicialObjectHomotopy.h_succ_comp_δ_castSucc_succ j) τ
  simpa only [hfun, CategoryTheory.comp_apply] using h2

lemma zsmul_negOnePow (k : ℕ) (r : R) : ((-1 : ℤ) ^ k) • r = (-1 : R) ^ k * r := by
  rw [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]

lemma telescope_sum {R : Type} [CommRing R] {m : ℕ}
    (G : Fin (m+3) → Fin (m+2) → R) (z w : R)
    (hmid : ∀ j : Fin (m+1), G (j.castSucc.succ) j.succ = G (j.castSucc.succ) j.castSucc)
    (h0 : G 0 0 = z) (hlast : G (Fin.last (m+2)) (Fin.last (m+1)) = w) :
    ∑ k : Fin (m+2), (G k.castSucc k - G k.succ k) = z - w := by
  have hB : ∑ k : Fin (m+2), G k.castSucc k
      = G 0 0 + ∑ j : Fin (m+1), G (j.castSucc.succ) (j.succ) := by
    rw [Fin.sum_univ_succ]
    rw [show (((0 : Fin (m+2)).castSucc)) = (0 : Fin (m+3)) from Fin.ext rfl]
    simp only [Fin.succ_castSucc]
  have hA : ∑ k : Fin (m+2), G k.succ k
      = (∑ j : Fin (m+1), G (j.castSucc.succ) (j.succ)) + G (Fin.last (m+2)) (Fin.last (m+1)) := by
    rw [Fin.sum_univ_castSucc]
    rw [show ((Fin.last (m+1)).succ) = (Fin.last (m+2)) from Fin.ext rfl]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hmid j]
  rw [Finset.sum_sub_distrib, hB, hA, h0, hlast]
  ring

/-- The cochain homotopy (prism operator): for `u : C^{m+1}(T)` this is the `m`-cochain on `S`
sending `σ` to `∑_a (-1)^a u (h_a σ)`. -/
noncomputable def hcochain (H : SSet.Homotopy f g) (m : ℕ) (u : Cochain T R (m+1)) :
    Cochain S R m :=
  fun σ => ∑ a : Fin (m+1), (-1 : R) ^ (a : ℕ) * u (hfun H m a σ)

/-- The prism identity: on cocycles `u` the coboundary of the cochain homotopy is
`g^* u - f^* u`. -/
lemma coboundary_hcochain (H : SSet.Homotopy f g) (m : ℕ) (u : Cochain T R (m+1))
    (hu : u ∈ cycles T R (m+1)) :
    coboundary S R m (hcochain H m u) = pullbackCo R g u - pullbackCo R f u := by
  ext τ
  have hL : coboundary S R m (hcochain H m u) τ
      = ∑ i : Fin (m+2), ∑ a : Fin (m+1),
          (-1 : R) ^ (i : ℕ) * ((-1 : R) ^ (a : ℕ) * u (hfun H m a (S.δ i τ))) := by
    rw [Submission.Cohomology.coboundary_apply]
    simp only [hcochain, zsmul_negOnePow, Finset.mul_sum]
  rw [hL]
  have h1 : ∀ a b, b.val ≤ a.val → u (hfun H m a (S.δ b τ))
      = u (T.δ b.castSucc (hfun H (m+1) a.succ τ)) := by
    intro a b hab
    exact (congrArg u (hfun_succ_δ H b a
      (Fin.le_iff_val_le_val.mpr (by simpa using hab)) τ)).symm
  have h2 : ∀ a b, a.val < b.val → u (hfun H m a (S.δ b τ))
      = u (T.δ b.succ (hfun H (m+1) a.castSucc τ)) := by
    intro a b hab
    exact (congrArg u (hfun_castSucc_δ H b a
      (Fin.lt_def.mpr (by simpa using hab)) τ)).symm
  have hc : ∀ k : Fin (m+2),
      ∑ l : Fin (m+3), (-1 : R) ^ (l : ℕ) * u (T.δ l (hfun H (m+1) k τ)) = 0 := by
    intro k
    have hp : coboundary T R (m+1) u = 0 := (Submission.Cohomology.mem_cycles_iff u).mp hu
    have h := congrArg (fun w => w (hfun H (m+1) k τ)) hp
    simpa only [Submission.Cohomology.coboundary_apply, Pi.zero_apply, zsmul_negOnePow] using h
  rw [prism_sum (fun a b => u (hfun H m a (S.δ b τ)))
        (fun l k => u (T.δ l (hfun H (m+1) k τ))) h1 h2 hc]
  have hmid : ∀ j : Fin (m+1),
      u (T.δ (j.castSucc.succ) (hfun H (m+1) j.succ τ))
        = u (T.δ (j.castSucc.succ) (hfun H (m+1) j.castSucc τ)) :=
    fun j => congrArg u (hfun_mid H j τ)
  have h0 : u (T.δ (0 : Fin (m+3)) (hfun H (m+1) (0 : Fin (m+2)) τ))
      = u (g.app (op ⦋m+1⦌) τ) := congrArg u (hfun_zero H (m+1) τ)
  have hlast : u (T.δ (Fin.last (m+2)) (hfun H (m+1) (Fin.last (m+1)) τ))
      = u (f.app (op ⦋m+1⦌) τ) := congrArg u (hfun_last H (m+1) τ)
  rw [telescope_sum (fun l k => u (T.δ l (hfun H (m+1) k τ)))
        (u (g.app (op ⦋m+1⦌) τ)) (u (f.app (op ⦋m+1⦌) τ)) hmid h0 hlast]
  simp only [Pi.sub_apply, Submission.Cohomology.pullbackCo_apply]

/-- Homotopic maps induce the same map of cochain complexes: the difference of the pullbacks of a
cocycle is a coboundary. -/
lemma pullbackCo_sub_mem_boundaries (H : SSet.Homotopy f g) (n : ℕ) (u : Cochain T R n)
    (hu : u ∈ cycles T R n) :
    pullbackCo R f u - pullbackCo R g u ∈ boundaries S R n := by
  cases n with
  | zero =>
      rw [show boundaries S R 0 = (⊥ : Submodule R (Cochain S R 0)) from rfl,
        Submodule.mem_bot]
      ext σ
      simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero,
        Submission.Cohomology.pullbackCo_apply]
      have hp : coboundary T R 0 u = 0 := (Submission.Cohomology.mem_cycles_iff u).mp hu
      have h := congrArg (fun w => w (hfun H 0 (0 : Fin 1) σ)) hp
      rw [Submission.Cohomology.coboundary_apply] at h
      simp only [Pi.zero_apply] at h
      have h' : ∑ i : Fin 2, (-1:ℤ)^(i:ℕ) • u (T.δ i (hfun H 0 (0 : Fin 1) σ)) = 0 := h
      simp only [zsmul_negOnePow, Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
        pow_zero, pow_one, one_mul, neg_one_mul] at h'
      have hx : u (T.δ (0 : Fin 2) (hfun H 0 0 σ))
          = u (T.δ (1 : Fin 2) (hfun H 0 0 σ)) :=
        sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact h')
      rw [hfun_zero H 0 σ] at hx
      have hfl : T.δ (1 : Fin 2) (hfun H 0 0 σ) = f.app (op ⦋0⦌) σ := by
        have h' := hfun_last H 0 σ
        simpa using h'
      rw [hfl] at hx
      exact hx.symm
  | succ m =>
      rw [show boundaries S R (m+1) = LinearMap.range (coboundary S R m) from rfl,
        LinearMap.mem_range]
      refine ⟨- hcochain H m u, ?_⟩
      rw [map_neg, coboundary_hcochain H m u hu]
      abel

theorem H_map_homotopic {S T : SSet.{0}} {R : Type} [CommRing R] {f g : S ⟶ T}
    (H : SSet.Homotopy f g) (n : ℕ) :
    Submission.Cohomology.H.map R f n = Submission.Cohomology.H.map R g n := by
  apply LinearMap.ext
  intro x
  refine Quotient.inductionOn x ?_
  intro a
  change Submission.Cohomology.H.map R f n (Submission.Cohomology.H.mk a.1 a.2)
      = Submission.Cohomology.H.map R g n (Submission.Cohomology.H.mk a.1 a.2)
  rw [Submission.Cohomology.H.map_mk, Submission.Cohomology.H.map_mk,
    Submission.Cohomology.H.mk_eq_mk_iff]
  exact pullbackCo_sub_mem_boundaries H n a.1 a.2

end Work.Cohomology
