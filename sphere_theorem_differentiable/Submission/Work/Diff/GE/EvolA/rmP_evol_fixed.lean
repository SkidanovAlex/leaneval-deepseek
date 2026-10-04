import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.Evol.curv_variation
import Submission.Work.Diff.Evol.curv_evolution
import Submission.Work.Diff.Evol.rmP_fixed_deriv
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.reaction_map_defs
import Submission.Work.Diff.GE.fixRmDefs
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.Evol.ricArr_rmFrame_eq_ricAt
import Submission.Work.Diff.Evol.Calc
import Submission.Work.Diff.GE.kato_cov3RmExt_field

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Diff.GE.EvolA

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

/-! ## Small algebraic and frame-independent prerequisites -/

/-- `reactionMap` (of `reaction_map_defs`) is exactly the reaction map `rmReact = Q − Xact`
(of `fixRmDefs`); the two definitions differ only in the order of the last two Ricci-action terms. -/
theorem reactionMap_eq_rmReact {n : ℕ} (R : Curv4 n) :
    Work.Diff.GE.reactionMap R = Work.Diff.GE.rmReact n R := by
  funext i j k l
  rw [Work.Diff.GE.rmReact_apply]
  show Submission.Diff.Alg.Q R i j k l - ∑ p, (Work.Diff.GE.ricF R i p * R p j k l
        + Work.Diff.GE.ricF R j p * R i p k l + Work.Diff.GE.ricF R l p * R i j k p
        + Work.Diff.GE.ricF R k p * R i j p l)
      = Submission.Diff.Alg.Q R i j k l - Work.Diff.Evol.Xact R i j k l
  rw [Work.Diff.Evol.Xact]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Work.Diff.GE.ricF, Work.Diff.Evol.ricArr]
  ring

/-- Combined linearity of `rmP` in its first slot. -/
theorem rmP_lin_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M) (r s : ℝ)
    (u v b c d : TangentSpace I x) :
    rmP g x (r • u + s • v) b c d = r * rmP g x u b c d + s * rmP g x v b c d := by
  rw [rmP_add_fst g hLC x (r • u) (s • v) b c d, rmP_smul_fst g hLC x r u b c d,
    rmP_smul_fst g hLC x s v b c d]

/-- Combined linearity of `rmP` in its second slot. -/
theorem rmP_lin_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M) (r s : ℝ)
    (a u v c d : TangentSpace I x) :
    rmP g x a (r • u + s • v) c d = r * rmP g x a u c d + s * rmP g x a v c d := by
  rw [rmP_add_snd g hLC x a (r • u) (s • v) c d, rmP_smul_snd g hLC x r a u c d,
    rmP_smul_snd g hLC x s a v c d]

/-- Combined linearity of `rmP` in its third slot. -/
theorem rmP_lin_thd (hLC : LCSmooth I M) (g : SMet I M) (x : M) (r s : ℝ)
    (a b u v d : TangentSpace I x) :
    rmP g x a b (r • u + s • v) d = r * rmP g x a b u d + s * rmP g x a b v d := by
  rw [rmP_add_thd g hLC x a b (r • u) (s • v) d, rmP_smul_thd g hLC x r a b u d,
    rmP_smul_thd g hLC x s a b v d]

/-- Combined linearity of `rmP` in its fourth slot. -/
theorem rmP_lin_fth (hLC : LCSmooth I M) (g : SMet I M) (x : M) (r s : ℝ)
    (a b c u v : TangentSpace I x) :
    rmP g x a b c (r • u + s • v) = r * rmP g x a b c u + s * rmP g x a b c v := by
  rw [rmP_add_fth g hLC x a b c (r • u) (s • v), rmP_smul_fth g hLC x r a b c u,
    rmP_smul_fth g hLC x s a b c v]

/-- Combined linearity of `lapRmAt` in its first slot. -/
theorem lapRmAt_lin_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M) (r s : ℝ)
    (u v b c d : TangentSpace I x) :
    Work.Diff.GE.lapRmAt g x (r • u + s • v) b c d
      = r * Work.Diff.GE.lapRmAt g x u b c d + s * Work.Diff.GE.lapRmAt g x v b c d := by
  have h1 : Work.Diff.GE.lapRmAt g x (r • u + s • v) b c d
      = ∑ z, cov2Rm g x (onFrame g x z) (onFrame g x z) (r • u + s • v) b c d := rfl
  have h2 : Work.Diff.GE.lapRmAt g x u b c d
      = ∑ z, cov2Rm g x (onFrame g x z) (onFrame g x z) u b c d := rfl
  have h3 : Work.Diff.GE.lapRmAt g x v b c d
      = ∑ z, cov2Rm g x (onFrame g x z) (onFrame g x z) v b c d := rfl
  rw [h1, h2, h3, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun z _ =>
    Work.Diff.GE.Kato3.cov2Rm_lin_thd hLC g x r s (onFrame g x z) (onFrame g x z) u v b c d

/-- Combined linearity of `lapRmAt` in its second slot. -/
theorem lapRmAt_lin_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M) (r s : ℝ)
    (a u v c d : TangentSpace I x) :
    Work.Diff.GE.lapRmAt g x a (r • u + s • v) c d
      = r * Work.Diff.GE.lapRmAt g x a u c d + s * Work.Diff.GE.lapRmAt g x a v c d := by
  have h1 : Work.Diff.GE.lapRmAt g x a (r • u + s • v) c d
      = ∑ z, cov2Rm g x (onFrame g x z) (onFrame g x z) a (r • u + s • v) c d := rfl
  have h2 : Work.Diff.GE.lapRmAt g x a u c d
      = ∑ z, cov2Rm g x (onFrame g x z) (onFrame g x z) a u c d := rfl
  have h3 : Work.Diff.GE.lapRmAt g x a v c d
      = ∑ z, cov2Rm g x (onFrame g x z) (onFrame g x z) a v c d := rfl
  rw [h1, h2, h3, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun z _ =>
    Work.Diff.GE.Kato3.cov2Rm_lin_fth hLC g x r s (onFrame g x z) (onFrame g x z) a u v c d

/-- Combined linearity of `lapRmAt` in its third slot. -/
theorem lapRmAt_lin_thd (hLC : LCSmooth I M) (g : SMet I M) (x : M) (r s : ℝ)
    (a b u v d : TangentSpace I x) :
    Work.Diff.GE.lapRmAt g x a b (r • u + s • v) d
      = r * Work.Diff.GE.lapRmAt g x a b u d + s * Work.Diff.GE.lapRmAt g x a b v d := by
  have h1 : Work.Diff.GE.lapRmAt g x a b (r • u + s • v) d
      = ∑ z, cov2Rm g x (onFrame g x z) (onFrame g x z) a b (r • u + s • v) d := rfl
  have h2 : Work.Diff.GE.lapRmAt g x a b u d
      = ∑ z, cov2Rm g x (onFrame g x z) (onFrame g x z) a b u d := rfl
  have h3 : Work.Diff.GE.lapRmAt g x a b v d
      = ∑ z, cov2Rm g x (onFrame g x z) (onFrame g x z) a b v d := rfl
  rw [h1, h2, h3, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun z _ =>
    Work.Diff.GE.Kato3.cov2Rm_lin_fif hLC g x r s (onFrame g x z) (onFrame g x z) a b u v d

/-- Combined linearity of `lapRmAt` in its fourth slot. -/
theorem lapRmAt_lin_fth (hLC : LCSmooth I M) (g : SMet I M) (x : M) (r s : ℝ)
    (a b c u v : TangentSpace I x) :
    Work.Diff.GE.lapRmAt g x a b c (r • u + s • v)
      = r * Work.Diff.GE.lapRmAt g x a b c u + s * Work.Diff.GE.lapRmAt g x a b c v := by
  have h1 : Work.Diff.GE.lapRmAt g x a b c (r • u + s • v)
      = ∑ z, cov2Rm g x (onFrame g x z) (onFrame g x z) a b c (r • u + s • v) := rfl
  have h2 : Work.Diff.GE.lapRmAt g x a b c u
      = ∑ z, cov2Rm g x (onFrame g x z) (onFrame g x z) a b c u := rfl
  have h3 : Work.Diff.GE.lapRmAt g x a b c v
      = ∑ z, cov2Rm g x (onFrame g x z) (onFrame g x z) a b c v := rfl
  rw [h1, h2, h3, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun z _ =>
    Work.Diff.GE.Kato3.cov2Rm_lin_sixth hLC g x r s (onFrame g x z) (onFrame g x z) a b c u v

/-! ## Expansion of a four-slot multilinear form in a frame -/

/-- **Expansion of a four-slot multilinear form in a frame.**  If `α` are the coefficients of the
vectors in the frame `f` (`u = ∑ i, α i u • f i` for every `u`) and `φ` is additive and homogeneous
in each slot, then `φ` is the fourfold contraction of its values on the frame. -/
theorem expand_apply_of_basis
    (x : M)
    (α : Fin (Module.finrank ℝ E) → TangentSpace I x → ℝ)
    (f : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hα : ∀ u : TangentSpace I x, u = ∑ i, α i u • f i)
    (φ : TangentSpace I x → TangentSpace I x → TangentSpace I x → TangentSpace I x → ℝ)
    (h1 : ∀ (r s : ℝ) u v b c d, φ (r • u + s • v) b c d = r * φ u b c d + s * φ v b c d)
    (h2 : ∀ (r s : ℝ) a u v c d, φ a (r • u + s • v) c d = r * φ a u c d + s * φ a v c d)
    (h3 : ∀ (r s : ℝ) a b u v d, φ a b (r • u + s • v) d = r * φ a b u d + s * φ a b v d)
    (h4 : ∀ (r s : ℝ) a b c u v, φ a b c (r • u + s • v) = r * φ a b c u + s * φ a b c v)
    (a b c d : TangentSpace I x) :
    φ a b c d = ∑ i, ∑ j, ∑ k, ∑ l,
      (α i a * α j b * α k c * α l d) * φ (f i) (f j) (f k) (f l) := by
  have expand1 : ∀ (ψ : TangentSpace I x → ℝ)
      (hadd : ∀ u v, ψ (u + v) = ψ u + ψ v)
      (hsmul : ∀ (c : ℝ) u, ψ (c • u) = c * ψ u) (u : TangentSpace I x),
      ψ u = ∑ i, α i u * ψ (f i) := by
    intro ψ hadd hsmul u
    have h0 : ψ 0 = 0 := by
      have h := hsmul 0 (0 : TangentSpace I x)
      simpa using h
    have hkey : ∀ s : Finset (Fin (Module.finrank ℝ E)),
        ψ (∑ i ∈ s, α i u • f i) = ∑ i ∈ s, α i u * ψ (f i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using h0
      | insert i s hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, ih, hsmul]
    conv_lhs => rw [hα u]
    exact hkey Finset.univ
  rw [expand1 (fun u => φ u b c d) (fun u v => by simpa using h1 1 1 u v b c d)
        (fun q u => by simpa using h1 q 0 u (0 : TangentSpace I x) b c d) a]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [expand1 (fun u => φ (f i) u c d) (fun u v => by simpa using h2 1 1 (f i) u v c d)
    (fun q u => by simpa using h2 q 0 (f i) u (0 : TangentSpace I x) c d) b]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [expand1 (fun u => φ (f i) (f j) u d) (fun u v => by simpa using h3 1 1 (f i) (f j) u v d)
    (fun q u => by simpa using h3 q 0 (f i) (f j) u (0 : TangentSpace I x) d) c]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [expand1 (fun u => φ (f i) (f j) (f k) u) (fun u v => by simpa using h4 1 1 (f i) (f j) (f k) u v)
    (fun q u => by simpa using h4 q 0 (f i) (f j) (f k) u (0 : TangentSpace I x)) d]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- Splitting a fourfold contraction of a sum of two four-slot arrays. -/
theorem sum4_mul_add {n : ℕ} (L R c : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, c i j k l * (L i j k l + R i j k l))
      = (∑ i, ∑ j, ∑ k, ∑ l, c i j k l * L i j k l)
        + (∑ i, ∑ j, ∑ k, ∑ l, c i j k l * R i j k l) := by
  have h4 : ∀ i j k : Fin n, (∑ l, c i j k l * (L i j k l + R i j k l))
      = (∑ l, c i j k l * L i j k l) + (∑ l, c i j k l * R i j k l) := by
    intro i j k
    rw [show (∑ l, c i j k l * (L i j k l + R i j k l))
          = ∑ l, (c i j k l * L i j k l + c i j k l * R i j k l) from
        Finset.sum_congr rfl fun l _ => by ring]
    exact Finset.sum_add_distrib
  have h3 : ∀ i j : Fin n,
      (∑ k, ∑ l, c i j k l * (L i j k l + R i j k l))
        = (∑ k, ∑ l, c i j k l * L i j k l) + (∑ k, ∑ l, c i j k l * R i j k l) := by
    intro i j
    rw [show (∑ k, ∑ l, c i j k l * (L i j k l + R i j k l))
          = ∑ k, ((∑ l, c i j k l * L i j k l) + (∑ l, c i j k l * R i j k l)) from
        Finset.sum_congr rfl fun k _ => h4 i j k]
    exact Finset.sum_add_distrib
  have h2 : ∀ i : Fin n,
      (∑ j, ∑ k, ∑ l, c i j k l * (L i j k l + R i j k l))
        = (∑ j, ∑ k, ∑ l, c i j k l * L i j k l)
          + (∑ j, ∑ k, ∑ l, c i j k l * R i j k l) := by
    intro i
    rw [show (∑ j, ∑ k, ∑ l, c i j k l * (L i j k l + R i j k l))
          = ∑ j, ((∑ k, ∑ l, c i j k l * L i j k l)
              + (∑ k, ∑ l, c i j k l * R i j k l)) from
        Finset.sum_congr rfl fun j _ => h3 i j]
    exact Finset.sum_add_distrib
  rw [show (∑ i, ∑ j, ∑ k, ∑ l, c i j k l * (L i j k l + R i j k l))
        = ∑ i, ((∑ j, ∑ k, ∑ l, c i j k l * L i j k l)
            + (∑ j, ∑ k, ∑ l, c i j k l * R i j k l)) from
      Finset.sum_congr rfl fun i _ => h2 i]
  exact Finset.sum_add_distrib

/-! ## The frame-vector derivatives -/

/-- At a `G t`-orthonormal frame, the componentwise time derivative of the curvature is the
Laplacian plus the reaction map `rmReact`. -/
theorem rmP_frame_deriv (hLC : LCSmooth I M) (hLV : LCVariation I M)
    (G : ℝ → SMet I M) (T : ℝ) (hflow : IsRicciFlow G T) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (heON : IsONFrame (G t) x e)
    (hn : 0 < Module.finrank ℝ E) :
    ∀ i j k l : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s ↦ rmP (G s) x (e i) (e j) (e k) (e l))
        (lapRmFrame (G t) x e i j k l
          + Work.Diff.GE.rmReact (Module.finrank ℝ E) (rmFrame (G t) x e) i j k l) t := by
  have hCV : CurvVariation I M := Work.Diff.Evol.curv_variation hLC hLV
  intro i j k l
  have hD := Work.Diff.Evol.rmP_fixed_deriv hLC hLV hCV G T hflow ht x
    (e i) (e j) (e k) (e l)
  have hval := Work.Diff.Evol.curvFrame_evolution_value hLC hLV hCV G T hflow ht x e heON hn
  have hval4 := congrFun (congrFun (congrFun (congrFun hval i) j) k) l
  simp only [Pi.add_apply] at hval4
  have hsum : (∑ p, (ricAt (lcOf (G t)) x (e i) (e p) * rmP (G t) x (e p) (e j) (e k) (e l)
        + ricAt (lcOf (G t)) x (e j) (e p) * rmP (G t) x (e i) (e p) (e k) (e l)
        + ricAt (lcOf (G t)) x (e k) (e p) * rmP (G t) x (e i) (e j) (e p) (e l)
        + ricAt (lcOf (G t)) x (e l) (e p) * rmP (G t) x (e i) (e j) (e k) (e p)))
      = Work.Diff.Evol.Xact (rmFrame (G t) x e) i j k l := by
    simp only [Work.Diff.Evol.Xact,
      Work.Diff.Evol.ricArr_rmFrame_eq_ricAt (I := I) (M := M) hLC (G t) x e heON]
    simp only [Work.Diff.Evol.rmFrame_eq_rmP_evol]
  have hbracket : (-2 * ricAt (lcOf (G t)) x (rmVec (lcOf (G t)) x (e i) (e j) (e l)) (e k)
        + (G t).inner x (covDLC G t (smoothExt x (e i)) (smoothExt x (e j))
            (smoothExt x (e l)) x
          - covDLC G t (smoothExt x (e j)) (smoothExt x (e i)) (smoothExt x (e l)) x) (e k))
      = lapRmFrame (G t) x e i j k l
        + Work.Diff.GE.rmReact (Module.finrank ℝ E) (rmFrame (G t) x e) i j k l := by
    rw [Work.Diff.GE.rmReact_apply]
    linarith [hval4, hsum]
  exact hD.congr_deriv hbracket

/-- The time derivative of a constant-coefficient fourfold sum of moving frame components. -/
theorem sum_rmP_hasDerivAt (G : ℝ → SMet I M) (t : ℝ) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (a b c d : TangentSpace I x) (α : Fin (Module.finrank ℝ E) → TangentSpace I x → ℝ)
    (hDf : ∀ i j k l : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s ↦ rmP (G s) x (e i) (e j) (e k) (e l))
        (lapRmFrame (G t) x e i j k l
          + Work.Diff.GE.rmReact (Module.finrank ℝ E) (rmFrame (G t) x e) i j k l) t) :
    HasDerivAt
      (fun s : ℝ ↦ ∑ i, ∑ j, ∑ k, ∑ l,
        (α i a * α j b * α k c * α l d) * rmP (G s) x (e i) (e j) (e k) (e l))
      (∑ i, ∑ j, ∑ k, ∑ l, (α i a * α j b * α k c * α l d)
        * (lapRmFrame (G t) x e i j k l
            + Work.Diff.GE.rmReact (Module.finrank ℝ E) (rmFrame (G t) x e) i j k l)) t := by
  have hD3 : ∀ i j k : Fin (Module.finrank ℝ E), HasDerivAt
      (fun s : ℝ ↦ ∑ l, (α i a * α j b * α k c * α l d)
        * rmP (G s) x (e i) (e j) (e k) (e l))
      (∑ l, (α i a * α j b * α k c * α l d)
        * (lapRmFrame (G t) x e i j k l
            + Work.Diff.GE.rmReact (Module.finrank ℝ E) (rmFrame (G t) x e) i j k l)) t := by
    intro i j k
    exact HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      (A := fun l ↦ fun s : ℝ ↦ (α i a * α j b * α k c * α l d)
        * rmP (G s) x (e i) (e j) (e k) (e l))
      (A' := fun l ↦ (α i a * α j b * α k c * α l d)
        * (lapRmFrame (G t) x e i j k l
            + Work.Diff.GE.rmReact (Module.finrank ℝ E) (rmFrame (G t) x e) i j k l))
      (fun l _ ↦ (hDf i j k l).const_mul (α i a * α j b * α k c * α l d))
  have hD2 : ∀ i j : Fin (Module.finrank ℝ E), HasDerivAt
      (fun s : ℝ ↦ ∑ k, ∑ l, (α i a * α j b * α k c * α l d)
        * rmP (G s) x (e i) (e j) (e k) (e l))
      (∑ k, ∑ l, (α i a * α j b * α k c * α l d)
        * (lapRmFrame (G t) x e i j k l
            + Work.Diff.GE.rmReact (Module.finrank ℝ E) (rmFrame (G t) x e) i j k l)) t := by
    intro i j
    exact HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      (A := fun k ↦ fun s : ℝ ↦ ∑ l, (α i a * α j b * α k c * α l d)
        * rmP (G s) x (e i) (e j) (e k) (e l))
      (A' := fun k ↦ ∑ l, (α i a * α j b * α k c * α l d)
        * (lapRmFrame (G t) x e i j k l
            + Work.Diff.GE.rmReact (Module.finrank ℝ E) (rmFrame (G t) x e) i j k l))
      (fun k _ ↦ hD3 i j k)
  have hD1 : ∀ i : Fin (Module.finrank ℝ E), HasDerivAt
      (fun s : ℝ ↦ ∑ j, ∑ k, ∑ l, (α i a * α j b * α k c * α l d)
        * rmP (G s) x (e i) (e j) (e k) (e l))
      (∑ j, ∑ k, ∑ l, (α i a * α j b * α k c * α l d)
        * (lapRmFrame (G t) x e i j k l
            + Work.Diff.GE.rmReact (Module.finrank ℝ E) (rmFrame (G t) x e) i j k l)) t := by
    intro i
    exact HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      (A := fun j ↦ fun s : ℝ ↦ ∑ k, ∑ l, (α i a * α j b * α k c * α l d)
        * rmP (G s) x (e i) (e j) (e k) (e l))
      (A' := fun j ↦ ∑ k, ∑ l, (α i a * α j b * α k c * α l d)
        * (lapRmFrame (G t) x e i j k l
            + Work.Diff.GE.rmReact (Module.finrank ℝ E) (rmFrame (G t) x e) i j k l))
      (fun j _ ↦ hD2 i j)
  exact HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
    (A := fun i ↦ fun s : ℝ ↦ ∑ j, ∑ k, ∑ l, (α i a * α j b * α k c * α l d)
      * rmP (G s) x (e i) (e j) (e k) (e l))
    (A' := fun i ↦ ∑ j, ∑ k, ∑ l, (α i a * α j b * α k c * α l d)
      * (lapRmFrame (G t) x e i j k l
          + Work.Diff.GE.rmReact (Module.finrank ℝ E) (rmFrame (G t) x e) i j k l))
    (fun i _ ↦ hD1 i)

/-! ## The main theorem -/

/-- **The fixed-vector curvature evolution.**  Along a Ricci flow the components of the curvature
tensor in fixed vectors satisfy `∂ₜ Rm = ΔRm + reactionMap(Rm)`, with `ΔRm = lapRmAt` the rough
Laplacian traced in a `G t`-orthonormal frame. -/
theorem rmP_evol_fixed
    (hLC : LCSmooth I M) (hLV : LCVariation I M) :
    ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M, ∀ a b c d : TangentSpace I x,
        HasDerivAt (fun s => rmP (G s) x a b c d)
          (Work.Diff.GE.lapRmAt (G t) x a b c d
            + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) x a b c d) t := by
  intro G T hflow t ht x a b c d
  by_cases hn : 0 < Module.finrank ℝ E
  · set e : Fin (Module.finrank ℝ E) → TangentSpace I x := onFrame (G t) x with he
    have heON : IsONFrame (G t) x e := Work.Diff.GE.isONFrame_onFrame (G t) x
    set α : Fin (Module.finrank ℝ E) → TangentSpace I x → ℝ :=
      fun i u ↦ (G t).inner x (e i) u with hαdef
    have hαapply : ∀ (i : Fin (Module.finrank ℝ E)) (u : TangentSpace I x),
        α i u = (G t).inner x (e i) u := by
      intro i u
      simp only [hαdef]
    have hα : ∀ u : TangentSpace I x, u = ∑ i, α i u • e i := by
      intro u
      rw [show (∑ i, α i u • e i) = ∑ i, (G t).inner x (e i) u • e i from
        Finset.sum_congr rfl fun i _ => by rw [hαapply i u]]
      exact (Work.Diff.GE.sum_inner_smul_eq_self (G t) x hn e heON u).symm
    have hDf := rmP_frame_deriv hLC hLV G T hflow ht x e heON hn
    have hfun : (fun s : ℝ ↦ rmP (G s) x a b c d)
        = fun s : ℝ ↦ ∑ i, ∑ j, ∑ k, ∑ l,
            (α i a * α j b * α k c * α l d)
              * rmP (G s) x (e i) (e j) (e k) (e l) := by
      funext s
      exact expand_apply_of_basis x α e hα (fun a b c d ↦ rmP (G s) x a b c d)
        (fun r s' u v b c d ↦ rmP_lin_fst hLC (G s) x r s' u v b c d)
        (fun r s' a u v c d ↦ rmP_lin_snd hLC (G s) x r s' a u v c d)
        (fun r s' a b u v d ↦ rmP_lin_thd hLC (G s) x r s' a b u v d)
        (fun r s' a b c u v ↦ rmP_lin_fth hLC (G s) x r s' a b c u v)
        a b c d
    have hderiv := sum_rmP_hasDerivAt G t x e a b c d α hDf
    have hLap0 : ∀ (i j k l : Fin (Module.finrank ℝ E)),
        Work.Diff.GE.lapRmAt (G t) x (e i) (e j) (e k) (e l)
          = lapRmFrame (G t) x e i j k l := by
      intro i j k l
      have h1 : Work.Diff.GE.lapRmAt (G t) x (e i) (e j) (e k) (e l)
          = ∑ m, Work.Diff.GE.cov2Rm (G t) x (e m) (e m) (e i) (e j) (e k) (e l) := rfl
      have h2 : lapRmFrame (G t) x e i j k l
          = ∑ m, Submission.Diff.cov2Rm (G t) x (e m) (e m) (e i) (e j) (e k) (e l) := rfl
      rw [h1, h2]
      exact Finset.sum_congr rfl fun m _ =>
        Work.Diff.Evol.ricci_id_aux_cov2Rm_eq (G t) x (e m) (e m) (e i) (e j) (e k) (e l)
    have hLap1 : Work.Diff.GE.lapRmAt (G t) x a b c d
        = ∑ i, ∑ j, ∑ k, ∑ l, (α i a * α j b * α k c * α l d)
            * Work.Diff.GE.lapRmAt (G t) x (e i) (e j) (e k) (e l) := by
      exact expand_apply_of_basis x α e hα (fun a b c d ↦ Work.Diff.GE.lapRmAt (G t) x a b c d)
        (fun r s u v b c d ↦ lapRmAt_lin_fst hLC (G t) x r s u v b c d)
        (fun r s a u v c d ↦ lapRmAt_lin_snd hLC (G t) x r s a u v c d)
        (fun r s a b u v d ↦ lapRmAt_lin_thd hLC (G t) x r s a b u v d)
        (fun r s a b c u v ↦ lapRmAt_lin_fth hLC (G t) x r s a b c u v)
        a b c d
    have hLap : Work.Diff.GE.lapRmAt (G t) x a b c d
        = ∑ i, ∑ j, ∑ k, ∑ l,
            (α i a * α j b * α k c * α l d) * lapRmFrame (G t) x e i j k l := by
      rw [hLap1]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
          rw [hLap0 i j k l]
    have hReact : (∑ i, ∑ j, ∑ k, ∑ l,
            (α i a * α j b * α k c * α l d)
              * Work.Diff.GE.rmReact (Module.finrank ℝ E) (rmFrame (G t) x e) i j k l)
        = Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) x a b c d := by
      simp only [Work.Diff.GE.reactionFormAt, rmC, hαapply]
      rw [← he]
      rw [reactionMap_eq_rmReact (R := rmFrame (G t) x e)]
    have hsplit := sum4_mul_add
      (L := fun i j k l ↦ lapRmFrame (G t) x e i j k l)
      (R := fun i j k l ↦ Work.Diff.GE.rmReact (Module.finrank ℝ E) (rmFrame (G t) x e) i j k l)
      (c := fun i j k l ↦ α i a * α j b * α k c * α l d)
    rw [hfun, hLap, ← hReact, ← hsplit]
    exact hderiv
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    have hzero : ∀ v : TangentSpace I x, v = 0 := by
      have h : Module.finrank ℝ (TangentSpace I x) = 0 := h0
      exact finrank_zero_iff_forall_zero.mp h
    have ha : a = 0 := hzero a
    have hb : b = 0 := hzero b
    have hc : c = 0 := hzero c
    have hd : d = 0 := hzero d
    have hrmP : (fun s : ℝ ↦ rmP (G s) x a b c d) = fun _ : ℝ ↦ (0 : ℝ) := by
      funext s
      rw [ha, hb, hc, hd]
      simpa using (rmP_smul_fst (G s) hLC x (0 : ℝ) (0 : TangentSpace I x) 0 0 0)
    have hz : Work.Diff.GE.lapRmAt (G t) x a b c d
        + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) x a b c d = 0 := by
      haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h0]; infer_instance
      rw [ha, hb, hc, hd]
      simp [Work.Diff.GE.lapRmAt, Work.Diff.GE.reactionFormAt, Finset.univ_eq_empty]
    rw [hrmP, hz]
    exact hasDerivAt_const (c := (0 : ℝ)) t

end Work.Diff.GE.EvolA
