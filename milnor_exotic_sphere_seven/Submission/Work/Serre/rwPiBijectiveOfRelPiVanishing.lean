import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.RatHurewicz.LESConsequences
import Submission.Work.RatHurewicz.Excision
import Submission.Work.Serre.cylRelPi
import Submission.Work.Serre.hZeroOfPiZero
import Submission.Work.Serre.whiskerSquare
import Submission.Work.Serre.fst_eq_of_piMap_one_eq_one

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre

noncomputable section

variable {A W : Type} [TopologicalSpace A] [TopologicalSpace W]

/-! ## helpers -/

private theorem piMapN_eq_pimap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (k : ℕ) (x : X) (a : HomotopyGroup (Fin (k + 1)) X x) :
    piMapN f (k + 1) x a = Work.StemsB.πmap f k x a := by
  induction a using Quotient.inductionOn with
  | h p => rfl

private theorem piMapN_eq_pimap_fun {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (k : ℕ) (x : X) : piMapN f (k + 1) x = Work.StemsB.πmap f k x :=
  funext (piMapN_eq_pimap f k x)

private theorem pimap_surjective_of_subsingleton_relPi (i : C(A, W)) (a : A) (k : ℕ)
    (h : Subsingleton (HomotopyGroup (Fin (k + 1)) (Work.RatHurewicz.homotopyFibre i a)
      (Work.RatHurewicz.homotopyFibreBasepoint i a))) :
    Function.Surjective (Work.StemsB.πmap i (k + 1) a) := by
  haveI : Subsingleton (HomotopyGroup (Fin (k + 1)) (Work.RatHurewicz.homotopyFibre i a)
      ((Work.StemsB.fibreIncl (Work.RatHurewicz.homotopyFibreFst i a)
        ((Work.RatHurewicz.homotopyFibreFst i a) (Work.RatHurewicz.homotopyFibreBasepoint i a)))
        (Work.StemsB.fibrePoint (Work.RatHurewicz.homotopyFibreFst i a)
          (Work.RatHurewicz.homotopyFibreBasepoint i a)))) := h
  intro z
  have hF := Work.StemsB.les_exact_F (Work.RatHurewicz.homotopyFibreFst i a)
    (Work.RatHurewicz.homotopyFibreBasepoint i a) (Work.RatHurewicz.fibreHrel i a) k
  have hsurj : Function.Surjective (Work.StemsB.dMap (Work.RatHurewicz.homotopyFibreFst i a)
      (Work.RatHurewicz.homotopyFibreBasepoint i a) (Work.RatHurewicz.fibreHrel i a) k) :=
    fun u => (hF u).mp (Subsingleton.elim _ _)
  obtain ⟨x, hx⟩ := hsurj (Work.RatHurewicz.pairShiftHom i a k z)
  refine ⟨x, ?_⟩
  have h2 : Work.RatHurewicz.fibreDMap i a k x = Work.RatHurewicz.pairShiftHom i a k z := hx
  have h3 : Work.RatHurewicz.pairShiftHom i a k (Work.StemsB.πmap i (k + 1) a x)
      = Work.RatHurewicz.pairShiftHom i a k z := by
    rw [← h2, Work.RatHurewicz.fibreDMap_eq_pairShiftHom]
    rfl
  exact (Work.RatHurewicz.pairShiftHom_bijective i a k).1 h3

private theorem pimap_eq_one_of_fst_eq_one (i : C(A, W)) (a : A) (k : ℕ)
    (h : ∀ y : HomotopyGroup (Fin (k + 2)) (Work.RatHurewicz.homotopyFibre i a)
      (Work.RatHurewicz.homotopyFibreBasepoint i a),
      Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a) (k + 1)
        (Work.RatHurewicz.homotopyFibreBasepoint i a) y = 1)
    {x : HomotopyGroup (Fin (k + 2)) A a} (hx : Work.StemsB.πmap i (k + 1) a x = 1) :
    x = 1 := by
  have hB := Work.StemsB.les_exact_B (Work.RatHurewicz.homotopyFibreFst i a)
    (Work.RatHurewicz.homotopyFibreBasepoint i a) (Work.RatHurewicz.fibreHrel i a) k
  have hd : Work.RatHurewicz.fibreDMap i a k x = 1 := by
    have h2 : Work.RatHurewicz.fibreDMap i a k x
        = Work.RatHurewicz.pairShiftHom i a k (Work.StemsB.πmap i (k + 1) a x) := by
      rw [Work.RatHurewicz.fibreDMap_eq_pairShiftHom]
      rfl
    rw [h2, hx, map_one]
  obtain ⟨w, hw⟩ := (hB x).mp hd
  rw [← hw]
  exact h w

private theorem pimap_injective_of_fst_eq_one (i : C(A, W)) (a : A) (k : ℕ)
    (h : ∀ y : HomotopyGroup (Fin (k + 2)) (Work.RatHurewicz.homotopyFibre i a)
      (Work.RatHurewicz.homotopyFibreBasepoint i a),
      Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a) (k + 1)
        (Work.RatHurewicz.homotopyFibreBasepoint i a) y = 1) :
    Function.Injective (Work.StemsB.πmap i (k + 1) a) := by
  intro x y hxy
  have h1 : Work.StemsB.πmap i (k + 1) a (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  exact mul_inv_eq_one.mp (pimap_eq_one_of_fst_eq_one i a k h h1)

private theorem fst_eq_one_of_subsingleton (i : C(A, W)) (a : A) (k : ℕ)
    (h : Subsingleton (HomotopyGroup (Fin (k + 2)) (Work.RatHurewicz.homotopyFibre i a)
      (Work.RatHurewicz.homotopyFibreBasepoint i a))) :
    ∀ y : HomotopyGroup (Fin (k + 2)) (Work.RatHurewicz.homotopyFibre i a)
      (Work.RatHurewicz.homotopyFibreBasepoint i a),
      Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a) (k + 1)
        (Work.RatHurewicz.homotopyFibreBasepoint i a) y = 1 :=
  fun y => by rw [h.elim y 1, map_one]

/-! ## degree 0 -/

private theorem joined_of_genLoopZero_homotopic {X : Type} [TopologicalSpace X] {x p q : X}
    (h : GenLoop.Homotopic (genLoopZero X x p) (genLoopZero X x q)) : Joined p q := by
  obtain ⟨H⟩ := h
  exact ⟨Path.mk ⟨fun t => H (t, fun _ => 0),
    H.continuous.comp (continuous_id.prodMk continuous_const)⟩
    (H.map_zero_left (fun _ => 0)) (H.map_one_left (fun _ => 0))⟩

private theorem genLoopZero_eq_iff {X : Type} [TopologicalSpace X] {x p q : X} :
    ((⟦genLoopZero X x p⟧ : HomotopyGroup (Fin 0) X x) = ⟦genLoopZero X x q⟧) ↔ Joined p q :=
  ⟨fun h => joined_of_genLoopZero_homotopic (Quotient.exact h),
    fun h => Quotient.sound (genLoopZero_homotopic h.some)⟩

private theorem eq_genLoopZero {X : Type} [TopologicalSpace X] {x : X} (γ : Ω^ (Fin 0) X x) :
    γ = genLoopZero X x (γ (fun _ => 0)) := by
  apply GenLoop.ext
  intro u
  show γ u = γ (fun _ => 0)
  exact congrArg γ (Subsingleton.elim u (fun _ => 0))

private theorem joined_of_joined_image (i : C(A, W)) (b b' : A)
    (h : Subsingleton (HomotopyGroup (Fin 0) (Work.RatHurewicz.homotopyFibre i b)
      (Work.RatHurewicz.homotopyFibreBasepoint i b))) (hb : Joined (i b) (i b')) :
    Joined b b' := by
  obtain ⟨γ⟩ := hb
  have hjoin : Joined (Work.RatHurewicz.homotopyFibreBasepoint i b)
      (⟨(b', ⟨γ.toContinuousMap, γ.source'⟩), γ.target'⟩ :
        Work.RatHurewicz.homotopyFibre i b) :=
    (genLoopZero_eq_iff (x := Work.RatHurewicz.homotopyFibreBasepoint i b)).mp (h.elim _ _)
  have hmap : Joined ((Work.RatHurewicz.homotopyFibreFst i b)
        (Work.RatHurewicz.homotopyFibreBasepoint i b))
      ((Work.RatHurewicz.homotopyFibreFst i b)
        (⟨(b', ⟨γ.toContinuousMap, γ.source'⟩), γ.target'⟩ :
          Work.RatHurewicz.homotopyFibre i b)) :=
    hjoin.map (Work.RatHurewicz.homotopyFibreFst i b).continuous
  exact hmap

private theorem piMapN_zero_injective (i : C(A, W)) (a : A)
    (h : ∀ b : A, Subsingleton (HomotopyGroup (Fin 0) (Work.RatHurewicz.homotopyFibre i b)
      (Work.RatHurewicz.homotopyFibreBasepoint i b))) :
    Function.Injective (piMapN i 0 a) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h γ =>
    induction y using Quotient.inductionOn with
    | h γ' =>
      obtain ⟨p⟩ : Joined (i (γ (fun _ => 0))) (i (γ' (fun _ => 0))) := by
        have h2 : (⟦genLoopZero W (i a) (i (γ (fun _ => 0)))⟧ : HomotopyGroup (Fin 0) W (i a))
            = ⟦genLoopZero W (i a) (i (γ' (fun _ => 0)))⟧ := by
          have h3 := hxy
          rw [show (⟦γ⟧ : HomotopyGroup (Fin 0) A a)
                = ⟦genLoopZero A a (γ (fun _ => 0))⟧ from congrArg _ (eq_genLoopZero γ),
            show (⟦γ'⟧ : HomotopyGroup (Fin 0) A a)
                = ⟦genLoopZero A a (γ' (fun _ => 0))⟧ from congrArg _ (eq_genLoopZero γ'),
            piMapN_zero_genLoopZero, piMapN_zero_genLoopZero] at h3
          exact h3
        exact genLoopZero_eq_iff.mp h2
      obtain ⟨p'⟩ : Joined (γ (fun _ => 0)) (γ' (fun _ => 0)) :=
        joined_of_joined_image i _ _ (h _) ⟨p⟩
      apply Quotient.sound
      rw [eq_genLoopZero γ, eq_genLoopZero γ']
      exact genLoopZero_homotopic p'

private theorem piMapN_zero_surjective (i : C(A, W)) (a : A)
    (hconn : ∀ w : W, ∃ a' : A, Nonempty (Path w (i a'))) :
    Function.Surjective (piMapN i 0 a) := by
  intro z
  induction z using Quotient.inductionOn with
  | h γ =>
    obtain ⟨a', ha'⟩ := hconn (γ (fun _ => 0))
    refine ⟨⟦genLoopZero A a a'⟧, ?_⟩
    rw [piMapN_zero_genLoopZero, eq_genLoopZero γ]
    apply Quotient.sound
    exact genLoopZero_homotopic ha'.some.symm

/-! ## degree 1 -/

private theorem piMapN_one_injective (i : C(A, W)) (a : A)
    (h : ∀ y : HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a)
      (Work.RatHurewicz.homotopyFibreBasepoint i a),
      Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a) 0
        (Work.RatHurewicz.homotopyFibreBasepoint i a) y = 1) :
    Function.Injective (piMapN i 1 a) := by
  intro x y hxy
  have hxy' : Work.StemsB.πmap i 0 a x = Work.StemsB.πmap i 0 a y := by
    rw [← piMapN_eq_pimap i 0 a x, ← piMapN_eq_pimap i 0 a y]
    exact hxy
  have h1 : Work.StemsB.πmap i 0 a (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy', mul_inv_cancel]
  obtain ⟨z, hz⟩ := fst_eq_of_piMap_one_eq_one i a (x * y⁻¹) h1
  exact mul_inv_eq_one.mp (hz.symm.trans (h z))

private theorem finOne_boundary {u : Fin 1 → unitInterval} (hu : u ∈ Cube.boundary (Fin 1)) :
    u = (fun _ => 0) ∨ u = (fun _ => 1) := by
  obtain ⟨j, hj | hj⟩ := hu
  · left
    funext i
    rw [Subsingleton.elim i j]
    exact hj
  · right
    funext i
    rw [Subsingleton.elim i j]
    exact hj

private theorem piMapN_one_surjective (i : C(A, W)) (a : A)
    (h : Subsingleton (HomotopyGroup (Fin 0) (Work.RatHurewicz.homotopyFibre i a)
      (Work.RatHurewicz.homotopyFibreBasepoint i a))) :
    Function.Surjective (piMapN i 1 a) := by
  rw [piMapN_eq_pimap_fun]
  intro z
  induction z using Quotient.inductionOn with
  | h γ =>
    let γp : Path (i a) (i a) :=
      ⟨⟨fun t => γ (fun _ => t), γ.1.continuous.comp (continuous_pi (fun _ => continuous_id))⟩,
        γ.2 (fun _ => 0) ⟨0, Or.inl rfl⟩, γ.2 (fun _ => 1) ⟨0, Or.inr rfl⟩⟩
    let q : Work.RatHurewicz.homotopyFibre i a := Work.Serre.fibrePointOf i γp
    have hjoin : Joined (Work.RatHurewicz.homotopyFibreBasepoint i a) q :=
      (genLoopZero_eq_iff (x := Work.RatHurewicz.homotopyFibreBasepoint i a)).mp (h.elim _ _)
    obtain ⟨η⟩ := hjoin
    let Q : C(unitInterval × unitInterval, W) :=
      ((cylRelCMFamily i a).comp η.toContinuousMap).uncurry
    have hQ : ∀ (s t : unitInterval), Q (s, t) = (η s).1.2.1 t := fun s t => rfl
    have hbot : ∀ s : unitInterval, Q (s, 0) = i a := by
      intro s
      rw [hQ s 0]
      exact (η s).1.2.2
    have hleft : ∀ t : unitInterval, Q (0, t) = i a := by
      intro t
      have h1 : Q (0, t) = (Work.RatHurewicz.homotopyFibreBasepoint i a).1.2.1 t := by
        rw [hQ 0 t]
        exact congrArg (fun p : Work.RatHurewicz.homotopyFibre i a => p.1.2.1 t) η.source'
      rw [h1]
      rfl
    have hγ : ∀ t : unitInterval, Q (1, t) = γp t := by
      intro t
      have h1 : Q (1, t) = (q).1.2.1 t := by
        rw [hQ 1 t]
        exact congrArg (fun p : Work.RatHurewicz.homotopyFibre i a => p.1.2.1 t) η.target'
      rw [h1]
      rfl
    have hQ11 : Q (1, 1) = i a := by
      have h1 : Q (1, 1) = (q).1.2.1 1 := by
        rw [hQ 1 1]
        exact congrArg (fun p : Work.RatHurewicz.homotopyFibre i a => p.1.2.1 1) η.target'
      exact h1.trans (q).2
    let δ : Path (i a) (i a) :=
      ⟨⟨fun s => Q (s, 1), Q.continuous.comp (continuous_id.prodMk continuous_const)⟩,
        hleft 1, hQ11⟩
    have hδ : ∀ s : unitInterval, Q (s, 1) = δ s := fun s => rfl
    have hpath : Path.Homotopic γp δ := whiskerSquare Q hbot hleft γp δ hγ hδ
    let β : Ω^ (Fin 1) A a :=
      ⟨⟨fun u => (Work.RatHurewicz.homotopyFibreFst i a) (η (u 0)),
        (Work.RatHurewicz.homotopyFibreFst i a).continuous.comp
          (η.continuous.comp (continuous_apply 0))⟩,
        fun u hu => by
          rcases finOne_boundary hu with rfl | rfl
          · show (Work.RatHurewicz.homotopyFibreFst i a)
                (η ((fun _ : Fin 1 => (0 : unitInterval)) 0)) = a
            exact (congrArg (Work.RatHurewicz.homotopyFibreFst i a) η.source').trans rfl
          · show (Work.RatHurewicz.homotopyFibreFst i a)
                (η ((fun _ : Fin 1 => (1 : unitInterval)) 0)) = a
            exact (congrArg (Work.RatHurewicz.homotopyFibreFst i a) η.target').trans rfl⟩
    let δg : Ω^ (Fin 1) W (i a) :=
      ⟨⟨fun u => Q (u 0, 1),
        Q.continuous.comp ((continuous_apply 0).prodMk continuous_const)⟩,
        fun u hu => by
          rcases finOne_boundary hu with rfl | rfl
          · show Q ((fun _ : Fin 1 => (0 : unitInterval)) 0, 1) = i a
            exact hleft 1
          · show Q ((fun _ : Fin 1 => (1 : unitInterval)) 0, 1) = i a
            exact hQ11⟩
    have hδg : δg = Work.StemsB.genLoopMap i 1 β := by
      apply GenLoop.ext
      intro u
      show Q (u 0, 1) = i ((Work.RatHurewicz.homotopyFibreFst i a) (η (u 0)))
      rw [hQ (u 0) 1]
      exact (η (u 0)).2
    have hδpath : genLoopEquivOfUnique (Fin 1) δg = δ := by
      apply Path.ext
      funext s
      rfl
    have hγpath : genLoopEquivOfUnique (Fin 1) γ = γp := by
      apply Path.ext
      funext t
      rfl
    have hπ : (⟦γ⟧ : HomotopyGroup (Fin 1) W (i a)) = ⟦δg⟧ := by
      apply HomotopyGroup.pi1EquivFundamentalGroup.injective
      rw [show HomotopyGroup.pi1EquivFundamentalGroup (⟦γ⟧ : HomotopyGroup (Fin 1) W (i a))
          = Path.Homotopic.Quotient.mk (genLoopEquivOfUnique (Fin 1) γ) from rfl,
        show HomotopyGroup.pi1EquivFundamentalGroup (⟦δg⟧ : HomotopyGroup (Fin 1) W (i a))
          = Path.Homotopic.Quotient.mk (genLoopEquivOfUnique (Fin 1) δg) from rfl,
        hγpath, hδpath]
      exact Quotient.sound hpath
    refine ⟨⟦β⟧, ?_⟩
    rw [Work.StemsB.πmap_apply_mk, ← hδg]
    exact hπ.symm



/-! ## The target -/

theorem rwPiBijectiveOfRelPiVanishing {A W : Type} [TopologicalSpace A] [TopologicalSpace W]
    (n : ℕ) (i : C(A, W))
    (hconn0 : ∀ w : W, ∃ a : A, Nonempty (Path w (i a)))
    (hconn : ∀ (a : A) (k : ℕ), k + 1 ≤ n + 1 →
      Subsingleton (Work.RatHurewicz.RelHomotopyGroup i a k))
    (htop : ∀ (a : A) (x : Work.RatHurewicz.RelHomotopyGroup i a (n + 1)),
      Work.Serre.piMapN (Work.RatHurewicz.homotopyFibreFst i a) (n + 1)
        (Work.RatHurewicz.homotopyFibreBasepoint i a) x = 1) :
    ∀ (q : ℕ), q ≤ n + 1 → ∀ a : A,
      Function.Bijective (Work.Serre.piMapN i q a) := by
  intro q hq a
  rcases q with _ | q'
  · exact ⟨piMapN_zero_injective i a (fun b => hconn b 0 (by omega)),
      piMapN_zero_surjective i a hconn0⟩
  rcases q' with _ | k
  · have hzero : ∀ y : HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a)
        (Work.RatHurewicz.homotopyFibreBasepoint i a),
        Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a) 0
          (Work.RatHurewicz.homotopyFibreBasepoint i a) y = 1 := by
      intro y
      rcases n with _ | n'
      · exact (piMapN_eq_pimap (Work.RatHurewicz.homotopyFibreFst i a) 0
          (Work.RatHurewicz.homotopyFibreBasepoint i a) y).symm.trans (htop a y)
      · haveI : Subsingleton (HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a)
            (Work.RatHurewicz.homotopyFibreBasepoint i a)) := hconn a 1 (by omega)
        rw [Subsingleton.elim y 1, map_one]
    exact ⟨piMapN_one_injective i a hzero,
      piMapN_one_surjective i a (hconn a 0 (by omega))⟩
  · have hmem : ∀ y : HomotopyGroup (Fin (k + 2)) (Work.RatHurewicz.homotopyFibre i a)
        (Work.RatHurewicz.homotopyFibreBasepoint i a),
        Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a) (k + 1)
          (Work.RatHurewicz.homotopyFibreBasepoint i a) y = 1 := by
      intro y
      by_cases hcase : k + 2 ≤ n
      · exact fst_eq_one_of_subsingleton i a k (hconn a (k + 2) (by omega)) y
      · have hn : n = k + 1 := by omega
        subst hn
        exact (piMapN_eq_pimap (Work.RatHurewicz.homotopyFibreFst i a) (k + 1)
          (Work.RatHurewicz.homotopyFibreBasepoint i a) y).symm.trans (htop a y)
    have hbridge : piMapN i (k + 2) a = Work.StemsB.πmap i (k + 1) a :=
      funext (piMapN_eq_pimap i (k + 1) a)
    exact ⟨hbridge ▸ pimap_injective_of_fst_eq_one i a k hmem,
      hbridge ▸ pimap_surjective_of_subsingleton_relPi i a k (hconn a (k + 1) (by omega))⟩


end

end Work.Serre
