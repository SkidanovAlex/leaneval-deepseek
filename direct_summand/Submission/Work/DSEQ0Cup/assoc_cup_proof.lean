import Mathlib
import Submission.Work.DSEQ0.CupBasic

/-!
# Associativity of the Alexander–Whitney cup product on the Čech complex

This file proves `Work.DSEQ0Cup.assoc_cup_proof`: the Alexander–Whitney cup product
`Work.DSEQ0.Cup.cup` on Mathlib's Čech complex `DSMap.cech A X f U` is associative, up to the
reindexing isomorphism `XIsoOfEq (Nat.add_assoc p q r)`.

The proof is a componentwise computation: rewriting the projection `proj` at an index `z`
through `proj_XIsoOfEq`, `proj_cup_apply`, `cupComp`, `res_mul` and `res_comp` reduces both sides
to a product of the three restricted components of `a`, `b`, `c`, grouped as
`(A * B) * C` and `A * (B * C)` respectively, where the front/middle/back index maps agree by
`Nat.add_assoc`. The two groupings are then equal by `mul_assoc` in the section ring.
-/

open CategoryTheory AlgebraicGeometry Limits
open scoped Simplicial

namespace Work.DSEQ0Cup

universe a

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

/-- The reindexing `Fin (((p+q)+r)+1) → Fin ((p+(q+r))+1)` induced by `Nat.add_assoc`. -/
abbrev acφ (p q r : ℕ) : Fin (((p+q)+r)+1) → Fin ((p+(q+r))+1) :=
  Fin.cast (congrArg (fun t => t+1) (Nat.add_assoc p q r))

private lemma hA (p q r : ℕ) : ∀ i : Fin (p+1),
    acφ p q r (Work.DSEQ0.Cup.frontIdx (p+q) r (Work.DSEQ0.Cup.frontIdx p q i))
      = Work.DSEQ0.Cup.frontIdx p (q+r) i := by
  intro i; apply Fin.ext; simp [acφ, Work.DSEQ0.Cup.frontIdx]

private lemma hB (p q r : ℕ) : ∀ j : Fin (q+1),
    acφ p q r (Work.DSEQ0.Cup.frontIdx (p+q) r (Work.DSEQ0.Cup.backIdx p q j))
      = Work.DSEQ0.Cup.backIdx p (q+r) (Work.DSEQ0.Cup.frontIdx q r j) := by
  intro j; apply Fin.ext; simp [acφ, Work.DSEQ0.Cup.frontIdx, Work.DSEQ0.Cup.backIdx]

private lemma hC (p q r : ℕ) : ∀ k : Fin (r+1),
    acφ p q r (Work.DSEQ0.Cup.backIdx (p+q) r k)
      = Work.DSEQ0.Cup.backIdx p (q+r) (Work.DSEQ0.Cup.backIdx q r k) := by
  intro k; apply Fin.ext; simp [acφ, Work.DSEQ0.Cup.backIdx]; omega

variable (A : Type a) [CommRing A] (X : AlgebraicGeometry.Scheme.{a})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) {ι : Type a} (U : ι → X.Opens)

/-- Combining two successive restriction maps (a version of `res_comp` stated on elements). -/
private lemma res_res {m n r : ℕ} (z : Fin (m+1) → ι) (φ : Fin (n+1) → Fin (m+1))
    (ψ : Fin (r+1) → Fin (n+1)) (x : ↥(Work.DSEQ0.Cup.frame A X f U r (fun k => z (φ (ψ k))))) :
    (Work.DSEQ0.Cup.res A X f U z φ).hom ((Work.DSEQ0.Cup.res A X f U (fun i => z (φ i)) ψ).hom x)
      = (Work.DSEQ0.Cup.res A X f U z (fun k => φ (ψ k))).hom x := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Work.DSEQ0.Cup.res_comp]

/-- The restricted component `(res z φ).hom ((proj (z ∘ φ)).hom x)` depends only on the index
function `φ`; a `φ = ψ` rewriting would otherwise be blocked by the dependent types, so we state
it as a homogeneous equality with `φ` and `ψ` as variables. -/
private lemma res_proj_congr {m n : ℕ} (z : Fin (m+1) → ι)
    {φ ψ : Fin (n+1) → Fin (m+1)} (h : φ = ψ)
    (x : ↥((DSMap.cech A X f U).X n)) :
    (Work.DSEQ0.Cup.res A X f U z φ).hom
        ((Work.DSEQ0.Cup.proj A X f U n (fun i => z (φ i))).hom x)
      = (Work.DSEQ0.Cup.res A X f U z ψ).hom
        ((Work.DSEQ0.Cup.proj A X f U n (fun i => z (ψ i))).hom x) := by
  subst h
  rfl

private lemma acφ_ff (p q r : ℕ) :
    (fun k : Fin (p+1) =>
        acφ p q r (Work.DSEQ0.Cup.frontIdx (p+q) r (Work.DSEQ0.Cup.frontIdx p q k)))
      = Work.DSEQ0.Cup.frontIdx p (q+r) := by
  funext k; exact hA p q r k

private lemma acφ_fb (p q r : ℕ) :
    (fun k : Fin (q+1) =>
        acφ p q r (Work.DSEQ0.Cup.frontIdx (p+q) r (Work.DSEQ0.Cup.backIdx p q k)))
      = (fun k : Fin (q+1) => Work.DSEQ0.Cup.backIdx p (q+r) (Work.DSEQ0.Cup.frontIdx q r k)) := by
  funext k; exact hB p q r k

private lemma acφ_bb (p q r : ℕ) :
    (fun k : Fin (r+1) => acφ p q r (Work.DSEQ0.Cup.backIdx (p+q) r k))
      = (fun k : Fin (r+1) =>
          Work.DSEQ0.Cup.backIdx p (q+r) (Work.DSEQ0.Cup.backIdx q r k)) := by
  funext k; exact hC p q r k

private lemma acφ_ff_z (p q r : ℕ) (z : Fin ((p+(q+r))+1) → ι) :
    (fun i : Fin (p+1) =>
        z (acφ p q r (Work.DSEQ0.Cup.frontIdx (p+q) r (Work.DSEQ0.Cup.frontIdx p q i))))
      = (fun i : Fin (p+1) => z (Work.DSEQ0.Cup.frontIdx p (q+r) i)) := by
  funext i; exact congrArg z (hA p q r i)

private lemma acφ_fb_z (p q r : ℕ) (z : Fin ((p+(q+r))+1) → ι) :
    (fun j : Fin (q+1) =>
        z (acφ p q r (Work.DSEQ0.Cup.frontIdx (p+q) r (Work.DSEQ0.Cup.backIdx p q j))))
      = (fun j : Fin (q+1) =>
          z (Work.DSEQ0.Cup.backIdx p (q+r) (Work.DSEQ0.Cup.frontIdx q r j))) := by
  funext j; exact congrArg z (hB p q r j)

private lemma acφ_bb_z (p q r : ℕ) (z : Fin ((p+(q+r))+1) → ι) :
    (fun k : Fin (r+1) => z (acφ p q r (Work.DSEQ0.Cup.backIdx (p+q) r k)))
      = (fun k : Fin (r+1) =>
          z (Work.DSEQ0.Cup.backIdx p (q+r) (Work.DSEQ0.Cup.backIdx q r k))) := by
  funext k; exact congrArg z (hC p q r k)

/-- The "flat" expansion of the triple cup product: the product of the three restricted
components of `a`, `b`, `c` in the section ring at `z`. -/
private noncomputable def cupFlat (p q r : ℕ)
    (a : ↥((DSMap.cech A X f U).X p)) (b : ↥((DSMap.cech A X f U).X q))
    (c : ↥((DSMap.cech A X f U).X r))
    (z : Fin ((p+(q+r))+1) → ι) : ↥(Work.DSEQ0.Cup.frame A X f U (p+(q+r)) z) :=
  (Work.DSEQ0.Cup.res A X f U z (Work.DSEQ0.Cup.frontIdx p (q+r))).hom
      ((Work.DSEQ0.Cup.proj A X f U p (fun i => z (Work.DSEQ0.Cup.frontIdx p (q+r) i))).hom a)
  * ((Work.DSEQ0.Cup.res A X f U z
          (fun k => Work.DSEQ0.Cup.backIdx p (q+r) (Work.DSEQ0.Cup.frontIdx q r k))).hom
        ((Work.DSEQ0.Cup.proj A X f U q
            (fun j => z (Work.DSEQ0.Cup.backIdx p (q+r) (Work.DSEQ0.Cup.frontIdx q r j)))).hom b)
     * (Work.DSEQ0.Cup.res A X f U z
          (fun k => Work.DSEQ0.Cup.backIdx p (q+r) (Work.DSEQ0.Cup.backIdx q r k))).hom
        ((Work.DSEQ0.Cup.proj A X f U r
            (fun j => z (Work.DSEQ0.Cup.backIdx p (q+r) (Work.DSEQ0.Cup.backIdx q r j)))).hom c))

theorem assoc_cup_proof (A : Type a) [CommRing A] (X : AlgebraicGeometry.Scheme.{a})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) {ι : Type a} (U : ι → X.Opens)
    (p q r : ℕ) (a : ↥((DSMap.cech A X f U).X p)) (b : ↥((DSMap.cech A X f U).X q))
    (c : ↥((DSMap.cech A X f U).X r)) :
    ((DSMap.cech A X f U).XIsoOfEq (Nat.add_assoc p q r)).hom
        (((Work.DSEQ0.Cup.cup A X f U (p+q) r) (((Work.DSEQ0.Cup.cup A X f U p q) a b)) c))
      = (Work.DSEQ0.Cup.cup A X f U p (q+r)) a (((Work.DSEQ0.Cup.cup A X f U q r) b c)) := by
  apply Work.DSEQ0.Cup.proj_ext A X f U
  intro z
  rw [Work.DSEQ0.Cup.proj_XIsoOfEq A X f U (Nat.add_assoc p q r) z]
  have hL : (Work.DSEQ0.Cup.res A X f U z (acφ p q r)).hom
        ((Work.DSEQ0.Cup.proj A X f U ((p+q)+r) (fun i => z (acφ p q r i))).hom
          (((Work.DSEQ0.Cup.cup A X f U (p+q) r) (((Work.DSEQ0.Cup.cup A X f U p q) a b)) c)))
      = cupFlat A X f U p q r a b c z := by
    rw [Work.DSEQ0.Cup.proj_cup_apply A X f U (p+q) r (Work.DSEQ0.Cup.cup A X f U p q a b) c
          (fun i => z (acφ p q r i))]
    rw [Work.DSEQ0.Cup.cupComp]
    rw [Work.DSEQ0.Cup.res_mul]
    rw [res_res A X f U]
    rw [Work.DSEQ0.Cup.proj_cup_apply A X f U p q a b
          (fun i => z (acφ p q r (Work.DSEQ0.Cup.frontIdx (p+q) r i)))]
    rw [Work.DSEQ0.Cup.cupComp]
    rw [Work.DSEQ0.Cup.res_mul]
    rw [res_res A X f U]
    rw [res_res A X f U]
    rw [res_res A X f U]
    rw [res_proj_congr A X f U z (acφ_ff p q r) a,
        res_proj_congr A X f U z (acφ_fb p q r) b,
        res_proj_congr A X f U z (acφ_bb p q r) c]
    rw [mul_assoc]
    rfl
  have hR : (Work.DSEQ0.Cup.proj A X f U (p+(q+r)) z).hom
        ((Work.DSEQ0.Cup.cup A X f U p (q+r)) a ((Work.DSEQ0.Cup.cup A X f U q r) b c))
      = cupFlat A X f U p q r a b c z := by
    rw [Work.DSEQ0.Cup.proj_cup_apply A X f U p (q+r) a (Work.DSEQ0.Cup.cup A X f U q r b c) z]
    rw [Work.DSEQ0.Cup.cupComp]
    rw [Work.DSEQ0.Cup.proj_cup_apply A X f U q r b c
          (fun j => z (Work.DSEQ0.Cup.backIdx p (q+r) j))]
    rw [Work.DSEQ0.Cup.cupComp]
    rw [Work.DSEQ0.Cup.res_mul]
    rw [res_res A X f U]
    rw [res_res A X f U]
    rfl
  rw [hL, hR]

end Work.DSEQ0Cup
