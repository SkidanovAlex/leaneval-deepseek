import Mathlib
import Submission.Work.Cohomology.CapH
import Submission.Work.Cohomology.cap_cup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R] (X : SSet)

lemma cast_apply_aux {A B : ℕ → Type*} (f : ∀ n, A n → B n) {a b : ℕ} (h : a = b) (x : A a) :
    h ▸ f a x = f b (h ▸ x) := by cases h; rfl

lemma chain_iCycles_injective (m : ℕ) :
    Function.Injective ((chainC R X).iCycles m) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

lemma iCycles_cochain_injective (n : ℕ) :
    Function.Injective ((cochainC R X).iCycles n) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

lemma iCycles_cycles_cast {a b : ℕ} (h : a = b) (w : ↑((chainC R X).cycles a)) :
    ((chainC R X).iCycles b) (h ▸ w) = h ▸ (((chainC R X).iCycles a) w) :=
  (cast_apply_aux (fun n (x : ↑((chainC R X).cycles n)) => ((chainC R X).iCycles n) x) h w).symm

lemma homologyπ_cycles_cast {a b : ℕ} (h : a = b) (w : ↑((chainC R X).cycles a)) :
    h ▸ (((chainC R X).homologyπ a) w) = ((chainC R X).homologyπ b) (h ▸ w) :=
  cast_apply_aux (fun n (x : ↑((chainC R X).cycles n)) => ((chainC R X).homologyπ n) x) h w

lemma iCycles_capPairZ_typed (n m : ℕ) (z : ↑((cochainC R X).cycles n))
    (c : ↑((chainC R X).cycles (n+m))) (α : Cochain R X n)
    (hα : α = ((cochainC R X).iCycles n) z) :
    ((chainC R X).iCycles m) (capPairZ R X n m z c)
      = cap R X α m (((chainC R X).iCycles (n+m)) c) := by
  subst hα
  exact capPairZ_iCycles R X n m z c

theorem capPair_cup_cycles (p q m : ℕ)
    (zx : ↑((cochainC R X).cycles p)) (zy : ↑((cochainC R X).cycles q))
    (w : ↑((chainC R X).cycles (p + (q + m)))) :
    capPair R X q m (((cochainC R X).homologyπ q) zy)
        (capPair R X p (q+m) (((cochainC R X).homologyπ p) zx)
          (((chainC R X).homologyπ (p+(q+m))) w))
      = capPair R X (p+q) m
          (cupH' R X p q (((cochainC R X).homologyπ p) zx)
            (((cochainC R X).homologyπ q) zy))
          ((Nat.add_assoc p q m) ▸ (((chainC R X).homologyπ (p+(q+m))) w)) := by
  set α : Cochain R X p := ((cochainC R X).iCycles p) zx with hα
  set β : Cochain R X q := ((cochainC R X).iCycles q) zy with hβ
  have hα0 : cochainDiff R X α = 0 := cochainDiff_iCycles R X p zx
  have hβ0 : cochainDiff R X β = 0 := cochainDiff_iCycles R X q zy
  let hcup : cochainDiff R X (cup R X α β) = 0 :=
    cochainDiff_cup_of_cocycles R X α β hα0 hβ0
  have hzx : cocycleOf R X α hα0 = zx := by
    apply iCycles_cochain_injective R X p
    rw [iCycles_cocycleOf R X α hα0]
  have hzy : cocycleOf R X β hβ0 = zy := by
    apply iCycles_cochain_injective R X q
    rw [iCycles_cocycleOf R X β hβ0]
  have hπp : ((cochainC R X).homologyπ p) zx = cohomologyClassOf R X α hα0 := by
    show ((cochainC R X).homologyπ p) zx = ((cochainC R X).homologyπ p) (cocycleOf R X α hα0)
    rw [hzx]
  have hπq : ((cochainC R X).homologyπ q) zy = cohomologyClassOf R X β hβ0 := by
    show ((cochainC R X).homologyπ q) zy = ((cochainC R X).homologyπ q) (cocycleOf R X β hβ0)
    rw [hzy]
  have hA : cupH' R X p q (((cochainC R X).homologyπ p) zx) (((cochainC R X).homologyπ q) zy)
      = ((cochainC R X).homologyπ (p+q)) (cocycleOf R X (cup R X α β) hcup) := by
    have h := cupH'_apply' R X α β hα0 hβ0
    rw [← hπp, ← hπq] at h
    exact h
  have hD : (Nat.add_assoc p q m) ▸ (((chainC R X).homologyπ (p+(q+m))) w)
      = ((chainC R X).homologyπ ((p+q)+m)) ((Nat.add_assoc p q m).symm ▸ w) :=
    homologyπ_cycles_cast R X (Nat.add_assoc p q m).symm w
  have hcast : ((chainC R X).iCycles ((p+q)+m)) ((Nat.add_assoc p q m).symm ▸ w)
      = (Nat.add_assoc p q m).symm ▸ (((chainC R X).iCycles (p+(q+m))) w) :=
    iCycles_cycles_cast R X (Nat.add_assoc p q m).symm w
  have hE : capPairZ R X q m zy (capPairZ R X p (q+m) zx w)
      = capPairZ R X (p+q) m (cocycleOf R X (cup R X α β) hcup)
          ((Nat.add_assoc p q m).symm ▸ w) := by
    apply chain_iCycles_injective R X m
    rw [iCycles_capPairZ_typed R X q m zy (capPairZ R X p (q+m) zx w) β hβ]
    rw [iCycles_capPairZ_typed R X p (q+m) zx w α hα]
    rw [iCycles_capPairZ_typed R X (p+q) m (cocycleOf R X (cup R X α β) hcup)
          ((Nat.add_assoc p q m).symm ▸ w) (cup R X α β)
          (iCycles_cocycleOf R X (cup R X α β) hcup).symm]
    rw [hcast]
    have hcap := cap_cup R X α β ((Nat.add_assoc p q m).symm ▸ (((chainC R X).iCycles (p+(q+m))) w))
    rw [eqRec_self_symm R X (Nat.add_assoc p q m) (((chainC R X).iCycles (p+(q+m))) w)] at hcap
    exact hcap.symm
  rw [capPair_apply R X p (q+m) zx w]
  rw [capPair_apply R X q m zy (capPairZ R X p (q+m) zx w)]
  rw [hA]
  rw [hD]
  rw [capPair_apply R X (p+q) m (cocycleOf R X (cup R X α β) hcup) ((Nat.add_assoc p q m).symm ▸ w)]
  rw [hE]

theorem capPair_cup (R : Type) [CommRing R] (X : SSet) (p q m : ℕ)
    (x : ↑((Work.Cohomology.cochainC R X).homology p))
    (y : ↑((Work.Cohomology.cochainC R X).homology q))
    (c : ↑((Work.Cohomology.chainC R X).homology (p + (q + m)))) :
    Work.Cohomology.capPair R X q m y (Work.Cohomology.capPair R X p (q + m) x c)
      = Work.Cohomology.capPair R X (p + q) m
          (Work.Cohomology.cupH' R X p q x y) ((Nat.add_assoc p q m) ▸ c) := by
  have hsurjC : ∀ n : ℕ, Function.Surjective
      (fun z : ↑((cochainC R X).cycles n) => ((cochainC R X).homologyπ n) z) :=
    fun n => (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hsurjH : ∀ n : ℕ, Function.Surjective
      (fun w : ↑((chainC R X).cycles n) => ((chainC R X).homologyπ n) w) :=
    fun n => (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨zx, hzx⟩ := hsurjC p x
  obtain ⟨zy, hzy⟩ := hsurjC q y
  obtain ⟨w, hw⟩ := hsurjH (p + (q + m)) c
  rw [← hzx, ← hzy, ← hw]
  exact capPair_cup_cycles R X p q m zx zy w

end
end Work.Cohomology
