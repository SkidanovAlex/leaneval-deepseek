import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.rank_poset_iff
import Submission.Commons.LinearAlgebra.Matrix.range_inf_range_sub_eq_bot
import Submission.Commons.LinearAlgebra.Matrix.range_sup_range_sub_eq
import Submission.Commons.LinearAlgebra.Matrix.rank_poset_trans
import Submission.Commons.LinearAlgebra.Submodule.exists_complement_pair_of_le_rank
import Submission.Commons.LinearAlgebra.LinearMap.card_hom_range_le_pow
import Submission.Commons.LinearAlgebra.LinearMap.card_hom_ker_le_pow

set_option maxHeartbeats 1600000

namespace Commons.LinearAlgebra.Matrix

open Module

/-- The two projections of an `IsCompl` decomposition sum to the identity. -/
theorem projection_add_projection {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (p q : Submodule F V) (h : IsCompl p q) (v : V) :
    ((p.projectionOnto q h) v : V) + ((q.projectionOnto p h.symm) v : V) = v := by
  have hva : v - ((p.projectionOnto q h) v : V) ∈ (p.projectionOnto q h).ker := by
    rw [LinearMap.mem_ker, map_sub,
      Submodule.projectionOnto_apply_left (h := h) (x := (p.projectionOnto q h) v)]
    exact sub_self _
  rw [Submodule.ker_projectionOnto] at hva
  have hb2 : ((q.projectionOnto p h.symm) (v - ((p.projectionOnto q h) v : V)) : V)
      = v - ((p.projectionOnto q h) v : V) := by
    rw [Submodule.projectionOnto_apply_left (h := h.symm)
      (x := ⟨v - ((p.projectionOnto q h) v : V), hva⟩)]
  have hbv : ((q.projectionOnto p h.symm) (v - ((p.projectionOnto q h) v : V)) : V)
      = ((q.projectionOnto p h.symm) v : V)
        - ((q.projectionOnto p h.symm) ((p.projectionOnto q h) v : V) : V) := by
    rw [map_sub]; rfl
  have hzero : (q.projectionOnto p h.symm) ((p.projectionOnto q h) v : V) = 0 :=
    Submodule.projectionOnto_apply_right (h := h.symm) (x := (p.projectionOnto q h) v)
  rw [hbv, hzero] at hb2
  simp only [Submodule.coe_zero, sub_zero] at hb2
  rw [hb2]; abel

/-- Graph lift: if `range Y ⊓ R = ⊥`, then `prR ∘ Y` factors (uniquely) through `prS ∘ Y`. -/
noncomputable def graphLift {F W V : Type*} [Field F] [AddCommGroup W] [Module F W]
    [AddCommGroup V] [Module F V] (R S : Submodule F V) (hRS : IsCompl R S)
    (Y : W →ₗ[F] V) (hY : LinearMap.range Y ⊓ R = ⊥) :
    ↥(LinearMap.range ((S.projectionOnto R hRS.symm).comp Y)) →ₗ[F] ↥R :=
  (Submodule.liftQ (LinearMap.ker ((S.projectionOnto R hRS.symm).comp Y))
      ((R.projectionOnto S hRS).comp Y) (by
        intro w hw
        rw [LinearMap.mem_ker] at hw ⊢
        have hwR : Y w ∈ R := by
          rw [← Submodule.ker_projectionOnto (h := hRS.symm), LinearMap.mem_ker]
          exact hw
        have hbot : Y w ∈ (⊥ : Submodule F V) := by
          rw [← hY]; exact ⟨LinearMap.mem_range_self _ w, hwR⟩
        rw [Submodule.mem_bot] at hbot
        simp only [LinearMap.comp_apply, hbot, map_zero])).comp
    (LinearMap.quotKerEquivRange
      ((S.projectionOnto R hRS.symm).comp Y)).symm.toLinearMap


theorem graphLift_apply {F W V : Type*} [Field F] [AddCommGroup W] [Module F W]
    [AddCommGroup V] [Module F V] (R S : Submodule F V) (hRS : IsCompl R S)
    (Y : W →ₗ[F] V) (hY : LinearMap.range Y ⊓ R = ⊥) (w : W) :
    graphLift R S hRS Y hY
        ⟨((S.projectionOnto R hRS.symm).comp Y) w, LinearMap.mem_range_self _ w⟩
      = ((R.projectionOnto S hRS).comp Y) w := by
  rw [graphLift, LinearMap.comp_apply]
  change (Submodule.liftQ (LinearMap.ker ((S.projectionOnto R hRS.symm).comp Y))
      ((R.projectionOnto S hRS).comp Y) _)
    ((LinearMap.quotKerEquivRange ((S.projectionOnto R hRS.symm).comp Y)).symm
      ⟨((S.projectionOnto R hRS.symm).comp Y) w, _⟩) = ((R.projectionOnto S hRS).comp Y) w
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- Uniqueness of the graph lift: any `Λ` with the same defining property equals `graphLift`. -/
theorem graphLift_unique {F W V : Type*} [Field F] [AddCommGroup W] [Module F W]
    [AddCommGroup V] [Module F V] (R S : Submodule F V) (hRS : IsCompl R S)
    (Y : W →ₗ[F] V) (hY : LinearMap.range Y ⊓ R = ⊥)
    (Λ : ↥(LinearMap.range ((S.projectionOnto R hRS.symm).comp Y)) →ₗ[F] ↥R)
    (hΛ : ∀ w, Λ ⟨((S.projectionOnto R hRS.symm).comp Y) w, LinearMap.mem_range_self _ w⟩
            = ((R.projectionOnto S hRS).comp Y) w) :
    Λ = graphLift R S hRS Y hY := by
  ext t
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp t.2
  have ht : t = ⟨((S.projectionOnto R hRS.symm).comp Y) w, LinearMap.mem_range_self _ w⟩ :=
    Subtype.ext hw.symm
  rw [ht, hΛ w, graphLift_apply]


/-- If `A - X` and `B - X` have the same `mulVecLin`, then `A = B`. -/
theorem eq_of_sub_mulVecLin_eq {n m : ℕ} (A B X : Matrix (Fin n) (Fin m) (ZMod 2))
    (h : (A - X).mulVecLin = (B - X).mulVecLin) : A = B := by
  have hsub : A - X = B - X := by
    ext i j
    have hc := congrArg (fun f : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) =>
      f (Pi.single j 1) i) h
    rwa [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
      Matrix.mulVec_single_one, Matrix.col_apply, Matrix.col_apply] at hc
  have := congrArg (fun M => M + X) hsub
  simpa using this

open Classical in
theorem card_rank_poset_upset_fiber_le_pow (n m d : ℕ) (X Z₀ : Matrix (Fin n) (Fin m) (ZMod 2))
    (hX : X.rank ≤ d) (hZ₀ : Z₀.rank = X.rank + (Z₀ - X).rank) :
    Nat.card {Z : Matrix (Fin n) (Fin m) (ZMod 2) //
      Z.rank = X.rank + (Z - X).rank ∧ Z.rank ≤ d ∧
      ∀ w : Fin m → ZMod 2, w ∈ LinearMap.ker X.mulVecLin →
        (Z - Z₀).mulVec w ∈ LinearMap.range X.mulVecLin} ≤ 2 ^ (2 * X.rank * d) := by
  classical
  set K : Submodule (ZMod 2) (Fin m → ZMod 2) := LinearMap.ker X.mulVecLin with hK
  set R : Submodule (ZMod 2) (Fin n → ZMod 2) := LinearMap.range X.mulVecLin with hR
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl K
  obtain ⟨S, hS⟩ := Submodule.exists_isCompl R
  set prR : (Fin n → ZMod 2) →ₗ[ZMod 2] ↥R := R.projectionOnto S hS with hprR
  set prS : (Fin n → ZMod 2) →ₗ[ZMod 2] ↥S := S.projectionOnto R hS.symm with hprS
  set D0 : ↥K →ₗ[ZMod 2] ↥S := (prS.comp (Z₀ - X).mulVecLin).comp K.subtype with hD0
  set SS := {Z : Matrix (Fin n) (Fin m) (ZMod 2) //
      Z.rank = X.rank + (Z - X).rank ∧ Z.rank ≤ d ∧
      ∀ w : Fin m → ZMod 2, w ∈ LinearMap.ker X.mulVecLin →
        (Z - Z₀).mulVec w ∈ LinearMap.range X.mulVecLin} with hSS
  have prS_ker : prS.ker = R := by rw [hprS]; exact Submodule.ker_projectionOnto (h := hS.symm)
  have prR_ker : prR.ker = S := by rw [hprR]; exact Submodule.ker_projectionOnto (h := hS)
  have prS_eq_zero : ∀ v : Fin n → ZMod 2, prS v = 0 ↔ v ∈ R := by
    intro v; rw [← LinearMap.mem_ker, prS_ker]
  have hYinf : ∀ Z : SS, LinearMap.range ((Z.1 - X).mulVecLin) ⊓ R = ⊥ := by
    intro Z
    rw [hR, inf_comm]
    exact range_inf_range_sub_eq_bot X Z.1 Z.2.1
  have hksup : ∀ Z : SS, K ⊔ LinearMap.ker ((Z.1 - X).mulVecLin) = ⊤ := by
    intro Z
    have hXY : X.mulVecLin + (Z.1 - X).mulVecLin = Z.1.mulVecLin := by
      rw [← Matrix.mulVecLin_add]; congr 1; abel
    have hrank : Module.finrank (ZMod 2) ↥(LinearMap.range (X.mulVecLin + (Z.1 - X).mulVecLin))
        = Module.finrank (ZMod 2) ↥(LinearMap.range X.mulVecLin)
          + Module.finrank (ZMod 2) ↥(LinearMap.range ((Z.1 - X).mulVecLin)) := by
      rw [hXY]; exact Z.2.1
    have h := (Commons.LinearAlgebra.Submodule.finrank_range_add_iff
      X.mulVecLin ((Z.1 - X).mulVecLin)).mp hrank
    rw [hK]; exact h.2.2.1
  have hkerPsi : ∀ Z : SS, LinearMap.ker (prS.comp ((Z.1 - X).mulVecLin))
      = LinearMap.ker ((Z.1 - X).mulVecLin) := by
    intro Z
    apply le_antisymm
    · intro w hw
      rw [LinearMap.mem_ker, LinearMap.comp_apply] at hw
      rw [LinearMap.mem_ker]
      have hmemR : ((Z.1 - X).mulVecLin) w ∈ R := (prS_eq_zero _).mp hw
      have hbot : ((Z.1 - X).mulVecLin) w ∈ (⊥ : Submodule (ZMod 2) (Fin n → ZMod 2)) := by
        rw [← hYinf Z]
        exact ⟨LinearMap.mem_range_self _ w, hmemR⟩
      rwa [Submodule.mem_bot] at hbot
    · intro w hw
      rw [LinearMap.mem_ker] at hw
      rw [LinearMap.mem_ker, LinearMap.comp_apply, hw, map_zero]
  have hPsiK : ∀ Z : SS, ∀ k : ↥K,
      (prS.comp ((Z.1 - X).mulVecLin)) (k : Fin m → ZMod 2) = D0 k := by
    intro Z k
    have hsub : (Z.1 - Z₀).mulVec (k : Fin m → ZMod 2) ∈ R := by
      rw [hR]; exact Z.2.2.2 (k : Fin m → ZMod 2) k.2
    have hsub' : ((Z.1 - X).mulVecLin - (Z₀ - X).mulVecLin) = (Z.1 - Z₀).mulVecLin := by
      apply LinearMap.ext; intro w
      rw [LinearMap.sub_apply, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
        Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec]
      abel
    have h2 : ((Z.1 - X).mulVecLin) (k : Fin m → ZMod 2)
        - ((Z₀ - X).mulVecLin) (k : Fin m → ZMod 2) = (Z.1 - Z₀).mulVec (k : Fin m → ZMod 2) := by
      rw [← LinearMap.sub_apply, hsub', Matrix.mulVecLin_apply]
    have hmemR : ((Z.1 - X).mulVecLin) (k : Fin m → ZMod 2)
        - ((Z₀ - X).mulVecLin) (k : Fin m → ZMod 2) ∈ R := by rw [h2]; exact hsub
    have h0 : prS (((Z.1 - X).mulVecLin) (k : Fin m → ZMod 2)
        - ((Z₀ - X).mulVecLin) (k : Fin m → ZMod 2)) = 0 := (prS_eq_zero _).mpr hmemR
    rw [map_sub] at h0
    rw [LinearMap.comp_apply, hD0, LinearMap.comp_apply]
    exact sub_eq_zero.mp h0
  have hrangeC : ∀ Z : SS,
      LinearMap.range ((prS.comp ((Z.1 - X).mulVecLin)).comp U.subtype) ≤ D0.range := by
    intro Z y hy
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hy
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    change prS (((Z.1 - X).mulVecLin) (u : Fin m → ZMod 2)) ∈ D0.range
    have hkw : (u : Fin m → ZMod 2) ∈ K ⊔ LinearMap.ker ((Z.1 - X).mulVecLin) := by
      rw [hksup Z]; exact Submodule.mem_top
    obtain ⟨k, hk, h, hh, hkh⟩ := Submodule.mem_sup.mp hkw
    have hD0k : prS (((Z.1 - X).mulVecLin) k) = D0 ⟨k, hk⟩ := by
      have h1 := hPsiK Z ⟨k, hk⟩
      rw [LinearMap.comp_apply] at h1; exact h1
    have hhk : prS (((Z.1 - X).mulVecLin) h) = 0 := by
      have h1 : ((Z.1 - X).mulVecLin) h = 0 := LinearMap.mem_ker.mp hh
      rw [h1, map_zero]
    rw [← hkh, map_add, map_add, hD0k, hhk, add_zero]
    exact LinearMap.mem_range_self D0 ⟨k, hk⟩
  have hkerB : ∀ Z : SS, D0.ker
      ≤ LinearMap.ker ((prR.comp ((Z.1 - X).mulVecLin)).comp K.subtype) := by
    intro Z y hy
    rw [LinearMap.mem_ker] at hy ⊢
    change prR (((Z.1 - X).mulVecLin) (y : Fin m → ZMod 2)) = 0
    have hprS_zero : prS (((Z.1 - X).mulVecLin) (y : Fin m → ZMod 2)) = 0 := by
      have h1 := hPsiK Z y
      rw [LinearMap.comp_apply] at h1
      rw [h1, hy]
    have hmemR : ((Z.1 - X).mulVecLin) (y : Fin m → ZMod 2) ∈ R := (prS_eq_zero _).mp hprS_zero
    have hmem : ((Z.1 - X).mulVecLin) (y : Fin m → ZMod 2)
        ∈ (⊥ : Submodule (ZMod 2) (Fin n → ZMod 2)) := by
      rw [← hYinf Z]
      exact ⟨LinearMap.mem_range_self _ _, hmemR⟩
    rw [Submodule.mem_bot] at hmem
    rw [hmem, map_zero]
  have htle : ∀ Z : SS, Module.finrank (ZMod 2) ↥D0.range ≤ d := by
    intro Z
    have heq : D0 = (prS.comp ((Z.1 - X).mulVecLin)).comp K.subtype := by
      apply LinearMap.ext; intro k; exact (hPsiK Z k).symm
    rw [heq]
    have hle_range : LinearMap.range ((prS.comp ((Z.1 - X).mulVecLin)).comp K.subtype)
        ≤ LinearMap.range (prS.comp ((Z.1 - X).mulVecLin)) := by
      rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_le_iff_le_comap]
      exact fun x _ => LinearMap.mem_range_self _ x
    have hf : Module.finrank (ZMod 2) ↥(LinearMap.range (prS.comp ((Z.1 - X).mulVecLin)))
        = Module.finrank (ZMod 2) ↥(LinearMap.range ((Z.1 - X).mulVecLin)) := by
      have e1 := LinearMap.finrank_range_add_finrank_ker (prS.comp ((Z.1 - X).mulVecLin))
      have e2 := LinearMap.finrank_range_add_finrank_ker ((Z.1 - X).mulVecLin)
      rw [hkerPsi Z] at e1
      omega
    calc Module.finrank (ZMod 2) ↥(LinearMap.range ((prS.comp ((Z.1 - X).mulVecLin)).comp K.subtype))
        ≤ Module.finrank (ZMod 2) ↥(LinearMap.range (prS.comp ((Z.1 - X).mulVecLin))) :=
          Submodule.finrank_mono hle_range
      _ = Module.finrank (ZMod 2) ↥(LinearMap.range ((Z.1 - X).mulVecLin)) := hf
      _ ≤ d := by
          show (Z.1 - X).rank ≤ d
          omega
  set T1 := {C : ↥U →ₗ[ZMod 2] ↥S // LinearMap.range C ≤ D0.range} with hT1
  set T2 := {B : ↥K →ₗ[ZMod 2] ↥R // D0.ker ≤ B.ker} with hT2
  let Φ : SS → T1 × T2 := fun Z =>
    (⟨(prS.comp ((Z.1 - X).mulVecLin)).comp U.subtype, hrangeC Z⟩,
     ⟨(prR.comp ((Z.1 - X).mulVecLin)).comp K.subtype, hkerB Z⟩)
  have hΦinj : Function.Injective Φ := by
    intro Z1 Z2 hh
    have hC : (prS.comp ((Z1.1 - X).mulVecLin)).comp U.subtype
        = (prS.comp ((Z2.1 - X).mulVecLin)).comp U.subtype :=
      congrArg (fun p : T1 × T2 => (p.1).1) hh
    have hB : (prR.comp ((Z1.1 - X).mulVecLin)).comp K.subtype
        = (prR.comp ((Z2.1 - X).mulVecLin)).comp K.subtype :=
      congrArg (fun p : T1 × T2 => (p.2).1) hh
    have hΨ : prS.comp ((Z1.1 - X).mulVecLin) = prS.comp ((Z2.1 - X).mulVecLin) := by
      apply LinearMap.ext; intro w
      have hw : w ∈ K ⊔ U := by rw [hU.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨k, hk, u, hu, hku⟩ := Submodule.mem_sup.mp hw
      have hkp : (prS.comp ((Z1.1 - X).mulVecLin)) k = (prS.comp ((Z2.1 - X).mulVecLin)) k := by
        rw [show (prS.comp ((Z1.1 - X).mulVecLin)) k = D0 ⟨k, hk⟩ from by
              rw [LinearMap.comp_apply]; exact hPsiK Z1 ⟨k, hk⟩,
            show (prS.comp ((Z2.1 - X).mulVecLin)) k = D0 ⟨k, hk⟩ from by
              rw [LinearMap.comp_apply]; exact hPsiK Z2 ⟨k, hk⟩]
      have hup : (prS.comp ((Z1.1 - X).mulVecLin)) u
          = (prS.comp ((Z2.1 - X).mulVecLin)) u := by
        have h1 := congrArg (fun f : ↥U →ₗ[ZMod 2] ↥S => f ⟨u, hu⟩) hC
        simpa using h1
      rw [← hku, map_add, map_add, hkp, hup]
    have hYeq : (Z1.1 - X).mulVecLin = (Z2.1 - X).mulVecLin := by
      apply LinearMap.ext; intro w
      have hw : w ∈ K ⊔ LinearMap.ker (prS.comp ((Z1.1 - X).mulVecLin)) := by
        rw [hkerPsi Z1, hksup Z1]; exact Submodule.mem_top
      obtain ⟨k, hk, h, hh, hkh⟩ := Submodule.mem_sup.mp hw
      have hh1 : ((Z1.1 - X).mulVecLin) h = 0 := by
        rw [← LinearMap.mem_ker, ← hkerPsi Z1]; exact hh
      have hh2 : ((Z2.1 - X).mulVecLin) h = 0 := by
        rw [← LinearMap.mem_ker, ← hkerPsi Z2, ← hΨ]; exact hh
      have f1 : ((Z1.1 - X).mulVecLin) w = ((Z1.1 - X).mulVecLin) k := by
        rw [← hkh, map_add, hh1, add_zero]
      have f2 : ((Z2.1 - X).mulVecLin) w = ((Z2.1 - X).mulVecLin) k := by
        rw [← hkh, map_add, hh2, add_zero]
      rw [f1, f2]
      have hpk : prS (((Z1.1 - X).mulVecLin) k) = prS (((Z2.1 - X).mulVecLin) k) := by
        have h1 := congrArg (fun f => f k) hΨ
        simpa only [LinearMap.comp_apply] using h1
      have hrk : prR (((Z1.1 - X).mulVecLin) k) = prR (((Z2.1 - X).mulVecLin) k) := by
        have h1 := congrArg (fun f : ↥K →ₗ[ZMod 2] ↥R => f ⟨k, hk⟩) hB
        simpa using h1
      have hk_eq : ((Z1.1 - X).mulVecLin) k = ((Z2.1 - X).mulVecLin) k := by
        refine sub_eq_zero.mp ?_
        have hmemR : ((Z1.1 - X).mulVecLin) k - ((Z2.1 - X).mulVecLin) k ∈ R := by
          rw [← prS_ker, LinearMap.mem_ker, map_sub, hpk, sub_self]
        have hmemS : ((Z1.1 - X).mulVecLin) k - ((Z2.1 - X).mulVecLin) k ∈ S := by
          rw [← prR_ker, LinearMap.mem_ker, map_sub, hrk, sub_self]
        have hbot : ((Z1.1 - X).mulVecLin) k - ((Z2.1 - X).mulVecLin) k
            ∈ (⊥ : Submodule (ZMod 2) (Fin n → ZMod 2)) := by
          rw [← hS.inf_eq_bot]; exact ⟨hmemR, hmemS⟩
        rwa [Submodule.mem_bot] at hbot
      exact hk_eq
    exact Subtype.ext (eq_of_sub_mulVecLin_eq Z1.1 Z2.1 X hYeq)
  by_cases hD : Module.finrank (ZMod 2) ↥D0.range ≤ d
  · haveI : Finite ↥U := inferInstance
    haveI : Finite ↥K := inferInstance
    haveI : Finite ↥R := inferInstance
    haveI : Finite ↥S := inferInstance
    haveI : Finite (↥U →ₗ[ZMod 2] ↥S) := Finite.of_injective
      (fun f : ↥U →ₗ[ZMod 2] ↥S => (f : ↥U → ↥S)) (fun a b h => LinearMap.ext (congrFun h))
    haveI : Finite (↥K →ₗ[ZMod 2] ↥R) := Finite.of_injective
      (fun f : ↥K →ₗ[ZMod 2] ↥R => (f : ↥K → ↥R)) (fun a b h => LinearMap.ext (congrFun h))
    haveI : Finite (T1 × T2) := inferInstance
    have hcard : Nat.card SS ≤ Nat.card (T1 × T2) := Nat.card_le_card_of_injective Φ hΦinj
    have hT1card : Nat.card T1
        = 2 ^ (Module.finrank (ZMod 2) ↥U * Module.finrank (ZMod 2) ↥D0.range) := by
      rw [hT1]
      have h := Commons.LinearAlgebra.LinearMap.card_hom_range_le_pow (K := ZMod 2)
        (A := ↥U) (B := ↥S) D0.range
      rwa [Nat.card_zmod] at h
    have hT2card : Nat.card T2
        = 2 ^ (Module.finrank (ZMod 2) ↥D0.range * Module.finrank (ZMod 2) ↥R) := by
      rw [hT2]
      have h := Commons.LinearAlgebra.LinearMap.card_hom_ker_le_pow (K := ZMod 2)
        (A := ↥K) (B := ↥R) (C := ↥S) D0
      rwa [Nat.card_zmod] at h
    have hRfin : Module.finrank (ZMod 2) ↥R = X.rank := by rw [hR]; rfl
    have hUfin : Module.finrank (ZMod 2) ↥U = X.rank := by
      have hKU : Module.finrank (ZMod 2) ↥K + Module.finrank (ZMod 2) ↥U = m := by
        have h := LinearEquiv.finrank_eq (Submodule.prodEquivOfIsCompl K U hU)
        rw [Module.finrank_prod, Module.finrank_fin_fun] at h
        exact h
      have hKR : Module.finrank (ZMod 2) ↥K + Module.finrank (ZMod 2) ↥R = m := by
        have h := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
        rw [← hK, ← hR, Module.finrank_fin_fun] at h
        omega
      have hRr : Module.finrank (ZMod 2) ↥R = X.rank := by rw [hR]; rfl
      omega
    calc Nat.card SS
        ≤ Nat.card (T1 × T2) := hcard
      _ = Nat.card T1 * Nat.card T2 := Nat.card_prod _ _
      _ = 2 ^ (Module.finrank (ZMod 2) ↥U * Module.finrank (ZMod 2) ↥D0.range)
            * 2 ^ (Module.finrank (ZMod 2) ↥D0.range * Module.finrank (ZMod 2) ↥R) := by
          rw [hT1card, hT2card]
      _ = 2 ^ (Module.finrank (ZMod 2) ↥U * Module.finrank (ZMod 2) ↥D0.range
            + Module.finrank (ZMod 2) ↥D0.range * Module.finrank (ZMod 2) ↥R) := by
          rw [← pow_add]
      _ = 2 ^ (X.rank * Module.finrank (ZMod 2) ↥D0.range
            + Module.finrank (ZMod 2) ↥D0.range * X.rank) := by rw [hUfin, hRfin]
      _ ≤ 2 ^ (2 * X.rank * d) := by
          apply Nat.pow_le_pow_right (by norm_num)
          have h1 : X.rank * Module.finrank (ZMod 2) ↥D0.range ≤ X.rank * d :=
            Nat.mul_le_mul_left _ hD
          have h2 : Module.finrank (ZMod 2) ↥D0.range * X.rank ≤ d * X.rank :=
            Nat.mul_le_mul_right _ hD
          nlinarith [h1, h2]
  · haveI : IsEmpty SS := ⟨fun Z => absurd (htle Z) hD⟩
    have h0 : Nat.card SS = 0 := Nat.card_eq_zero.mpr (Or.inl ‹IsEmpty SS›)
    rw [h0]; exact Nat.zero_le _

end Commons.LinearAlgebra.Matrix
