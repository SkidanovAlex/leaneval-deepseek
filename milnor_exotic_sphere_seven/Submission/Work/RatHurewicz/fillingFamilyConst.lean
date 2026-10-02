import Mathlib
import Submission.Work.RatHurewicz.CubicalDefs
import Submission.Work.RatHurewicz.FillFamilyDefs
import Submission.Work.RatHurewicz.PinchGeom
import Submission.Work.RatHurewicz.geomPinch
import Submission.Work.RatHurewicz.cubeBoundaryGlue
import Submission.Work.RatHurewicz.extensionOfBased
import Submission.Work.RatHurewicz.faceComm
import Submission.Work.RatHurewicz.pieceAgree
import Submission.Work.RatHurewicz.boundaryMap
import Submission.Work.RatHurewicz.boundaryMapOne
import Submission.Work.RatHurewicz.ConnectivityBridge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The filling family `K` of the cubical Hurewicz construction

`Work.RatHurewicz.fillingFamilyConst`: for a space `X` whose homotopy groups `π_i (X, x₀)` are
trivial for `i ≤ N`, there is a family of fillings
`K n : C(I^n, X) → C(I^{n+1}, X)` with

* `K n p` has top face `p` and bottom face the constant cube at `x₀` (for `n ≤ N`);
* the side faces of `K (n+1) p` are `K n` applied to the faces of `p` (for `n + 1 ≤ N`);
* `K n` of the constant cube is the constant cube (for `n ≤ N`).

The construction is by induction on the level, using `boundaryMap`/`boundaryMapOne` (the prescribed
boundary data glues) and `extensionOfBased` (a based null-homotopy extends the boundary data).
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The `n`-th operator of the filling family, together with its properties up to a given level. -/
structure Tower (x₀ : X) (N : ℕ) where
  Kf : (n : ℕ) → C(IC n, X) → C(IC (n + 1), X)
  hα : ∀ n, n ≤ N → ∀ p : C(IC n, X),
    (Kf n p).comp (faceCM (Fin.last n) 1) = p ∧
    (Kf n p).comp (faceCM (Fin.last n) 0) = cconst n x₀
  hβ : ∀ n, n + 1 ≤ N → ∀ (p : C(IC (n + 1), X)) (j : Fin (n + 1)),
    (Kf (n + 1) p).comp (faceCM (Fin.castSucc j) 0) = Kf n (p.comp (faceCM j 0)) ∧
    (Kf (n + 1) p).comp (faceCM (Fin.castSucc j) 1) = Kf n (p.comp (faceCM j 1))
  hγ : ∀ n, n ≤ N → Kf n (cconst n x₀) = cconst (n + 1) x₀


/-- The level-`0` operator: a path from `x₀` to each point. -/
theorem exists_Kf_zero (x₀ : X) (h0 : Subsingleton (HomotopyGroup (Fin 0) X x₀)) :
    ∃ K0 : C(IC 0, X) → C(IC 1, X),
      (∀ p : C(IC 0, X), (K0 p).comp (faceCM (Fin.last 0) 1) = p ∧
        (K0 p).comp (faceCM (Fin.last 0) 0) = cconst 0 x₀) ∧
      K0 (cconst 0 x₀) = cconst 1 x₀ := by
  classical
  haveI : PathConnectedSpace X := pathConnectedSpace_of_subsingleton_pi_zero x₀ h0
  refine ⟨fun p => if hp : p = cconst 0 x₀ then cconst 1 x₀ else
      ⟨fun t : IC 1 => (PathConnectedSpace.joined x₀ (p 0)).some (t 0), by fun_prop⟩, ?_, ?_⟩
  · intro p
    by_cases hp : p = cconst 0 x₀
    · subst hp
      dsimp only
      rw [dif_pos rfl]
      constructor
      · ext u
        simp only [ContinuousMap.comp_apply, cconst, ContinuousMap.const_apply]
      · ext u
        simp only [ContinuousMap.comp_apply, cconst, ContinuousMap.const_apply]
    · dsimp only
      rw [dif_neg hp]
      have hpt : ∀ u : IC 0, p u = p 0 := fun u => congrArg p (Subsingleton.elim u 0)
      constructor
      · ext u
        show (PathConnectedSpace.joined x₀ (p 0)).some ((faceCM (Fin.last 0) 1 u) 0) = p u
        have h1 : (faceCM (Fin.last 0) 1 u) 0 = 1 := by simp
        rw [h1, (PathConnectedSpace.joined x₀ (p 0)).some.target, hpt u]
      · ext u
        show (PathConnectedSpace.joined x₀ (p 0)).some ((faceCM (Fin.last 0) 0 u) 0) = x₀
        have h1 : (faceCM (Fin.last 0) 0 u) 0 = 0 := by simp
        rw [h1, (PathConnectedSpace.joined x₀ (p 0)).some.source]
  · dsimp only
    rw [dif_pos rfl]

/-- From the boundary data of the filling `K (L+1) p`, build the filling itself (a cube with the
prescribed faces), given that `π_{L+1} (X, x₀)` is trivial. -/
theorem exists_level (L : ℕ) (x₀ : X) (Kp : C(IC L, X) → C(IC (L + 1), X))
    (htriv : Subsingleton (HomotopyGroup (Fin (L + 1)) X x₀))
    (p : C(IC (L + 1), X)) (B : C(↥(Cube.boundary (Fin (L + 2))), X))
    (hBbot : B.comp (bface (L + 1) (Fin.last (L + 1)) 0) = cconst (L + 1) x₀)
    (hBtop : B.comp (bface (L + 1) (Fin.last (L + 1)) 1) = p)
    (hBside : ∀ (j : Fin (L + 1)) (b : Fin 2),
      B.comp (bface (L + 1) (Fin.castSucc j) b) = Kp (p.comp (faceCM j (cval b)))) :
    ∃ F : C(IC (L + 2), X),
      (F.comp (faceCM (Fin.last (L + 1)) 1) = p ∧
        F.comp (faceCM (Fin.last (L + 1)) 0) = cconst (L + 1) x₀) ∧
      (∀ (j : Fin (L + 1)) (b : Fin 2),
        F.comp (faceCM (Fin.castSucc j) (cval b)) = Kp (p.comp (faceCM j (cval b)))) := by
  have hm : 1 ≤ L + 1 := Nat.succ_le_succ (Nat.zero_le L)
  have hpin := geomPinch (L + 1) hm
  -- the boundary map is `x₀` on the bottom face
  have hBbot' : ∀ z : ↥(Cube.boundary (Fin (L + 2))),
      (z : IC (L + 2)) (Fin.last (L + 1)) = 0 → B z = x₀ := by
    intro z hz
    have h1 : z = bface (L + 1) (Fin.last (L + 1)) 0 (initC (L + 1) (z : IC (L + 2))) := by
      apply Subtype.ext
      rw [bface_apply, cval_zero]
      exact (faceCM_last_apply (L + 1) (z : IC (L + 2)) hz).symm
    rw [h1, ← ContinuousMap.comp_apply, hBbot]
    rfl
  -- the based cube given by the boundary data
  let g : GenLoop (Fin (L + 1)) X x₀ := ⟨B.comp (iota (L + 1) hm), by
    intro u hu
    simp only [ContinuousMap.comp_apply]
    exact hBbot' _ (hpin.2.1 u hu)⟩
  haveI : Subsingleton (Quotient (GenLoop.Homotopic.setoid (Fin (L + 1)) x₀)) := htriv
  have hHom : GenLoop.Homotopic g GenLoop.const :=
    Quotient.exact (Subsingleton.elim (Quotient.mk _ g) (Quotient.mk _ GenLoop.const))
  obtain ⟨Fh⟩ := hHom
  let G : C(unitInterval × IC (L + 1), X) := Fh.toHomotopy.toContinuousMap
  have hG0 : ∀ u : IC (L + 1), G (0, u) = B (iota (L + 1) hm u) := fun u =>
    Fh.toHomotopy.map_zero_left u
  have hG1 : ∀ u : IC (L + 1), G (1, u) = x₀ := by
    intro u
    exact (Fh.map_one_left u).trans rfl
  have hG2 : ∀ u ∈ Cube.boundary (Fin (L + 1)), ∀ s : unitInterval, G (s, u) = x₀ := by
    intro u hu s
    have h := Fh.prop s u hu
    exact h.trans (g.2 u hu)
  obtain ⟨F, hF⟩ := extensionOfBased (m := L + 1) hm x₀ B G hBbot' hG0 hG1 hG2 hpin.2.2.1 hpin.2.2.2
  refine ⟨F, ⟨?_, ?_⟩, ?_⟩
  · ext u
    rw [ContinuousMap.comp_apply]
    have h1 : F (faceCM (Fin.last (L + 1)) 1 u)
        = B (bface (L + 1) (Fin.last (L + 1)) 1 u) := by
      have h2 := hF (bface (L + 1) (Fin.last (L + 1)) 1 u)
      simpa using h2
    rw [h1, ← ContinuousMap.comp_apply, hBtop]
  · ext u
    rw [ContinuousMap.comp_apply]
    have h1 : F (faceCM (Fin.last (L + 1)) 0 u)
        = B (bface (L + 1) (Fin.last (L + 1)) 0 u) := by
      have h2 := hF (bface (L + 1) (Fin.last (L + 1)) 0 u)
      simpa using h2
    rw [h1, ← ContinuousMap.comp_apply, hBbot]
  · intro j b
    ext u
    rw [ContinuousMap.comp_apply]
    have h1 : F (faceCM (Fin.castSucc j) (cval b) u)
        = B (bface (L + 1) (Fin.castSucc j) b u) := by
      have h2 := hF (bface (L + 1) (Fin.castSucc j) b u)
      simpa using h2
    rw [h1, ← ContinuousMap.comp_apply, hBside]


/-- One step of the induction: from the tower up to level `L` build the tower up to level `L + 1`,
using the boundary data of `boundaryMap`/`boundaryMapOne` and the extension `exists_level`. -/
theorem Tower_succ (N L : ℕ) (x₀ : X)
    (hconn : ∀ i, i ≤ N → Subsingleton (HomotopyGroup (Fin i) X x₀))
    (hL : L + 1 ≤ N) (T : Tower x₀ L) : Nonempty (Tower x₀ (L + 1)) := by
  classical
  -- the filling of each `p`, from its boundary data
  have hper : ∀ p : C(IC (L + 1), X), ∃ F : C(IC (L + 2), X),
      (F.comp (faceCM (Fin.last (L + 1)) 1) = p ∧
        F.comp (faceCM (Fin.last (L + 1)) 0) = cconst (L + 1) x₀) ∧
      (∀ (j : Fin (L + 1)) (b : Fin 2),
        F.comp (faceCM (Fin.castSucc j) (cval b)) = T.Kf L (p.comp (faceCM j (cval b)))) := by
    intro p
    have hB : ∃ B : C(↥(Cube.boundary (Fin (L + 2))), X),
        B.comp (bface (L + 1) (Fin.last (L + 1)) 0) = cconst (L + 1) x₀ ∧
        B.comp (bface (L + 1) (Fin.last (L + 1)) 1) = p ∧
        (∀ (j : Fin (L + 1)) (b : Fin 2),
          B.comp (bface (L + 1) (Fin.castSucc j) b)
            = T.Kf L (p.comp (faceCM j (cval b)))) := by
      rcases Nat.eq_zero_or_pos L with h0 | hpos
      · subst h0
        obtain ⟨B, hBt, hBb, hBs⟩ := boundaryMapOne x₀ (T.Kf 0) p (fun q => T.hα 0 (by omega) q)
        exact ⟨B, hBb, hBt, hBs⟩
      · obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 :=
          ⟨L - 1, (Nat.succ_pred_eq_of_pos hpos).symm⟩
        have hβL : ∀ (q : C(IC (L' + 1), X)) (j : Fin (L' + 1)) (b : Fin 2),
            ((T.Kf (L' + 1)) q).comp (faceCM (Fin.castSucc j) (cval b))
              = (T.Kf L') (q.comp (faceCM j (cval b))) := by
          intro q j b
          have h := T.hβ L' (by omega) q j
          fin_cases b
          · simpa using h.1
          · simpa using h.2
        obtain ⟨B, hBt, hBb, hBs⟩ := boundaryMap (k := L') x₀ (T.Kf (L' + 1)) (T.Kf L') p
          (fun q => T.hα (L' + 1) (by omega) q) hβL
        exact ⟨B, hBb, hBt, hBs⟩
    obtain ⟨B, hBb, hBt, hBs⟩ := hB
    exact exists_level L x₀ (T.Kf L) (hconn (L + 1) hL) p B hBb hBt hBs
  choose F hF using hper
  -- the const-normalisation
  let newK : C(IC (L + 1), X) → C(IC (L + 2), X) :=
    fun p => if hp : p = cconst (L + 1) x₀ then cconst (L + 2) x₀ else F p
  have hnewα : ∀ p : C(IC (L + 1), X),
      (newK p).comp (faceCM (Fin.last (L + 1)) 1) = p ∧
      (newK p).comp (faceCM (Fin.last (L + 1)) 0) = cconst (L + 1) x₀ := by
    intro p
    by_cases hp : p = cconst (L + 1) x₀
    · subst hp
      have : newK (cconst (L + 1) x₀) = cconst (L + 2) x₀ := by simp [newK]
      rw [this]
      constructor <;> ext u <;> simp [cconst, ContinuousMap.const_apply]
    · have : newK p = F p := by simp only [newK]; rw [dif_neg hp]
      rw [this]; exact (hF p).1
  have hnewβ : ∀ (p : C(IC (L + 1), X)) (j : Fin (L + 1)) (b : Fin 2),
      (newK p).comp (faceCM (Fin.castSucc j) (cval b)) = T.Kf L (p.comp (faceCM j (cval b))) := by
    intro p j b
    by_cases hp : p = cconst (L + 1) x₀
    · subst hp
      have : newK (cconst (L + 1) x₀) = cconst (L + 2) x₀ := by simp [newK]
      rw [this]
      have hcomp : (cconst (L + 1) x₀).comp (faceCM j (cval b)) = cconst L x₀ := by
        ext u; simp [cconst, ContinuousMap.const_apply]
      rw [hcomp, T.hγ L (by omega)]
      ext u; simp [cconst, ContinuousMap.const_apply]
    · have : newK p = F p := by simp only [newK]; rw [dif_neg hp]
      rw [this]; exact (hF p).2 j b
  have hnewγ : newK (cconst (L + 1) x₀) = cconst (L + 2) x₀ := by simp [newK]
  -- the new tower
  let Kf' : (n : ℕ) → C(IC n, X) → C(IC (n + 1), X) :=
    fun n => if hn : n ≤ L then T.Kf n else if h : n = L + 1 then h ▸ newK else fun _ => cconst (n+1) x₀
  have hKf'_le : ∀ n, n ≤ L → Kf' n = T.Kf n := by
    intro n hn; simp only [Kf']; rw [dif_pos hn]
  have hKf'_new : Kf' (L + 1) = newK := by
    simp only [Kf']
    rw [dif_neg (by omega : ¬ L + 1 ≤ L)]
    simp
  refine ⟨{ Kf := Kf', hα := ?_, hβ := ?_, hγ := ?_ }⟩
  · intro n hn p
    rcases Nat.lt_or_ge n (L + 1) with h1 | h1
    · rw [hKf'_le n (by omega)]
      exact T.hα n (by omega) p
    · have hn' : n = L + 1 := by omega
      subst n
      rw [hKf'_new]
      exact hnewα p
  · intro n hn p j
    rcases Nat.lt_or_ge n L with h1 | h1
    · have h2 : n + 1 ≤ L := by omega
      rw [hKf'_le (n + 1) h2, hKf'_le n (by omega)]
      exact T.hβ n (by omega) p j
    · have hn' : n = L := by omega
      subst n
      rw [hKf'_new, hKf'_le L le_rfl]
      exact ⟨hnewβ p j 0, hnewβ p j 1⟩
  · intro n hn
    rcases Nat.lt_or_ge n (L + 1) with h1 | h1
    · rw [hKf'_le n (by omega)]
      exact T.hγ n (by omega)
    · have hn' : n = L + 1 := by omega
      subst n
      rw [hKf'_new]
      exact hnewγ

theorem fillingFamilyConst (N : ℕ) {X : Type} [TopologicalSpace X] (x₀ : X)
    (hconn : ∀ i, i ≤ N → Subsingleton (HomotopyGroup (Fin i) X x₀)) :
    ∃ K : (n : ℕ) → C(Work.Stems.Cubical.IC n, X) → C(Work.Stems.Cubical.IC (n+1), X),
      (∀ n, n ≤ N → ∀ p : C(Work.Stems.Cubical.IC n, X),
        (K n p).comp (Work.Stems.Cubical.faceCM (Fin.last n) 1) = p ∧
        (K n p).comp (Work.Stems.Cubical.faceCM (Fin.last n) 0) = Work.RatHurewicz.cconst n x₀) ∧
      (∀ n, n+1 ≤ N → ∀ (p : C(Work.Stems.Cubical.IC (n+1), X)) (j : Fin (n+1)),
        (K (n+1) p).comp (Work.Stems.Cubical.faceCM (Fin.castSucc j) 0)
            = K n (p.comp (Work.Stems.Cubical.faceCM j 0)) ∧
        (K (n+1) p).comp (Work.Stems.Cubical.faceCM (Fin.castSucc j) 1)
            = K n (p.comp (Work.Stems.Cubical.faceCM j 1))) ∧
      (∀ n, n ≤ N → K n (Work.RatHurewicz.cconst n x₀) = Work.RatHurewicz.cconst (n+1) x₀) := by
  have hmain : ∀ L, L ≤ N → Nonempty (Tower x₀ L) := by
    intro L
    induction L with
    | zero =>
      intro _
      obtain ⟨K0, hα0, hγ0⟩ := exists_Kf_zero x₀ (hconn 0 (Nat.zero_le N))
      refine ⟨{ Kf := fun n => if h : n = 0 then h ▸ K0 else fun _ => cconst (n + 1) x₀,
                hα := ?_, hβ := ?_, hγ := ?_ }⟩
      · intro n hn p
        have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
        subst n
        dsimp only
        rw [dif_pos rfl]
        exact hα0 p
      · intro n hn
        exact absurd hn (Nat.not_succ_le_zero n)
      · intro n hn
        have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
        subst n
        dsimp only
        rw [dif_pos rfl]
        exact hγ0
    | succ L ih =>
      intro hL
      exact Tower_succ N L x₀ hconn (by omega) (ih (by omega)).some
  obtain ⟨T⟩ := hmain N le_rfl
  exact ⟨T.Kf, T.hα, T.hβ, T.hγ⟩

end

end Work.RatHurewicz
