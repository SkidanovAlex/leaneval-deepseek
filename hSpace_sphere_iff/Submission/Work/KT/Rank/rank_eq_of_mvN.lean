import Mathlib
import Submission.Work.KT.Defs

namespace Work.KT.Rank

open Matrix

/-- Two Murray--von Neumann equivalent idempotent matrices have the same rank (the ranges of the
corresponding projections are isomorphic, via the witnesses `a`, `b`).  Idempotency is necessary:
without it the statement is false (`a * b * a = a` need not hold). -/
theorem rank_eq_of_mvN {n m : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin m) (Fin m) ℂ)
    (hP : P * P = P) (hQ : Q * Q = Q)
    (h : Work.KT.Mat.MvN (⟨n, P⟩ : Work.KT.Mat ℂ) (⟨m, Q⟩ : Work.KT.Mat ℂ)) :
    P.rank = Q.rank := by
  obtain ⟨a, b, hba, hab⟩ := h
  -- `P = b a` and `Q = a b` as linear endomorphisms acting on `Fin n → ℂ` and `Fin m → ℂ`.
  have hBA : b.mulVecLin.comp a.mulVecLin = P.mulVecLin := by
    rw [← Matrix.mulVecLin_mul, hba]
  have hAB : a.mulVecLin.comp b.mulVecLin = Q.mulVecLin := by
    rw [← Matrix.mulVecLin_mul, hab]
  have hBA' : ∀ y, b.mulVecLin (a.mulVecLin y) = P.mulVecLin y :=
    fun y => by simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hBA y
  have hAB' : ∀ y, a.mulVecLin (b.mulVecLin y) = Q.mulVecLin y :=
    fun y => by simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hAB y
  -- idempotency of the two endomorphisms
  have hPP' : ∀ y, P.mulVecLin (P.mulVecLin y) = P.mulVecLin y := by
    intro y
    have hPP : P.mulVecLin.comp P.mulVecLin = P.mulVecLin := by
      rw [← Matrix.mulVecLin_mul, hP]
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hPP y
  have hQQ' : ∀ y, Q.mulVecLin (Q.mulVecLin y) = Q.mulVecLin y := by
    intro y
    have hQQ : Q.mulVecLin.comp Q.mulVecLin = Q.mulVecLin := by
      rw [← Matrix.mulVecLin_mul, hQ]
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hQQ y
  -- `b ∘ a` is the identity on `range P`, `a ∘ b` is the identity on `range Q`
  have hIdP : ∀ y : Fin n → ℂ, y ∈ LinearMap.range P.mulVecLin →
      b.mulVecLin (a.mulVecLin y) = y := by
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    rw [hBA' (P.mulVecLin z), hPP' z]
  have hIdQ : ∀ y : Fin m → ℂ, y ∈ LinearMap.range Q.mulVecLin →
      a.mulVecLin (b.mulVecLin y) = y := by
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    rw [hAB' (Q.mulVecLin z), hQQ' z]
  -- `a` maps `range P` into `range Q` and `b` maps `range Q` into `range P`
  have hA_mem : ∀ y : Fin n → ℂ, y ∈ LinearMap.range P.mulVecLin →
      a.mulVecLin y ∈ LinearMap.range Q.mulVecLin := by
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    exact ⟨a.mulVecLin z, by rw [← hAB' (a.mulVecLin z), hBA' z]⟩
  have hB_mem : ∀ y : Fin m → ℂ, y ∈ LinearMap.range Q.mulVecLin →
      b.mulVecLin y ∈ LinearMap.range P.mulVecLin := by
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    exact ⟨b.mulVecLin z, by rw [← hBA' (b.mulVecLin z), hAB' z]⟩
  -- the two restrictions are mutually inverse linear maps of the ranges
  let f : (LinearMap.range P.mulVecLin) →ₗ[ℂ] (LinearMap.range Q.mulVecLin) :=
    (a.mulVecLin.domRestrict _).codRestrict _ (fun x => hA_mem x.1 x.2)
  let g : (LinearMap.range Q.mulVecLin) →ₗ[ℂ] (LinearMap.range P.mulVecLin) :=
    (b.mulVecLin.domRestrict _).codRestrict _ (fun x => hB_mem x.1 x.2)
  have hcomp1 : ∀ x : ↥(LinearMap.range Q.mulVecLin), f (g x) = x :=
    fun x => Subtype.ext (hIdQ x.1 x.2)
  have hcomp2 : ∀ x : ↥(LinearMap.range P.mulVecLin), g (f x) = x :=
    fun x => Subtype.ext (hIdP x.1 x.2)
  have hgf : f.comp g = LinearMap.id := by
    ext x : 1
    exact hcomp1 x
  have hfg : g.comp f = LinearMap.id := by
    ext x : 1
    exact hcomp2 x
  exact (LinearEquiv.ofLinearMap f g hgf hfg).finrank_eq

end Work.KT.Rank
