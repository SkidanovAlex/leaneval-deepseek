import Mathlib
import Submission.Work.Drive.projRot
import Submission.Work.Drive.contDiffOn_projTransFun
import Submission.Work.Drive.contMDiffAt_projMk
import Submission.Work.Drive.contMDiffAt_projChartMap

/-!
# The rotation of `ℝP³` is smooth in the rotation parameter

`Work.Drive.projRot t` is the projectivisation of the diagonal rotation `Work.Drive.diagRot t` of
`ℂ² ≅ ℝ⁴` (`Submission/Work/Drive/projRot.lean`).

The main theorem of this file is `Work.Drive.contMDiffAt_projRot_mk`: for a `C^∞` nowhere-vanishing
lift `V` of a map into `ℝP³`, the *rotated* family

`(t, x) ↦ projRot t [V x]`

(where the pair `(t,x)` is flattened into a single vector, so that the smoothness criterion for maps
into `ℝPⁿ` applies) is `C^∞` as well.  This is the smoothness input of the rotation action on the
capping space `Work.Drive.CappingSpace`
(`Work.Drive.contMDiff_rotCapping`, `Submission/Work/Drive/rotCappingSmooth.lean`), hence of the
*openness* clause of `Work.Drive.StripRel` and of the perturbation argument for the genericity
hypotheses of the counting engine.

The proof is the chain rule applied to the *lift*: `projRot t [V x] = [diagRot t (V x)]`, so
smoothness follows from `Work.Drive.contMDiffAt_projMk` once the lifted map
`(t,x) ↦ diagRot t (V x)` is known to be `C^∞` and nowhere zero.
-/


set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

namespace Work.Drive

open scoped LinearAlgebra.Projectivization Manifold ContDiff
open Set Filter

noncomputable section

/-! ## The standard section and the projective coordinates are smooth -/

/-- **The standard section `x ↦ (x, 1)` of the projective charts is smooth** (it is affine). -/
lemma contDiff_projSection (n : ℕ) (i : Fin (n + 1)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (projSection (n := n) i) := by
  rw [contDiff_piLp (p := 2) (E := fun _ : Fin (n + 1) => ℝ)]
  intro k
  exact (contDiff_projSection_ofLp n i k).of_le le_top

/-- **The projective coordinates are smooth where their denominator does not vanish.** -/
lemma contDiffAt_projCoordFun (n : ℕ) (i : Fin (n + 1)) (v : Eucl n) (hv : v.ofLp i ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (projCoordFun (n := n) i) v := by
  rw [contDiffAt_piLp (p := 2) (E := fun _ : Fin n => ℝ)]
  intro j
  have hnum : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : Eucl n => w.ofLp (i.succAbove j)) v :=
    contDiffAt_piLp_apply (p := 2) (E := fun _ : Fin (n + 1) => ℝ) (i := i.succAbove j)
  have hden : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : Eucl n => w.ofLp i) v :=
    contDiffAt_piLp_apply (p := 2) (E := fun _ : Fin (n + 1) => ℝ) (i := i)
  have hj : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : Eucl n => w.ofLp (i.succAbove j) / w.ofLp i) v :=
    hnum.div hden (by simpa using hv)
  simpa only [projCoordFun_ofLp] using hj

/-- **The sphere lift of a chart inverse.**  If `w ≠ 0` has non-zero `i`-th coordinate, then the
projective point `[w]` is the image of `projCoordFun i w` under the `i`-th chart. -/
lemma projChartInv_projCoordFun (n : ℕ) (i : Fin (n + 1)) {w : Eucl n} (hw : w ≠ 0)
    (hwi : w.ofLp i ≠ 0) :
    projChartInv i (projCoordFun i w) = Projectivization.mk ℝ w hw := by
  have hp : Projectivization.mk ℝ w hw ∈ projChartSource i :=
    (mem_projChartSource_iff' hw).mpr hwi
  rw [← projChartMap_mk i w hw]
  exact projChartInv_projChartMap hp

/-! ## The flattened parameter space -/

/-- The tail of a flattened vector: the vector of the last `k` coordinates of
`u : EuclideanSpace ℝ (Fin (k+1))`. -/
def tailVec {k : ℕ} (u : EuclideanSpace ℝ (Fin (k + 1))) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i : Fin k => u.ofLp i.succ)

lemma tailVec_ofLp {k : ℕ} (u : EuclideanSpace ℝ (Fin (k + 1))) (i : Fin k) :
    (tailVec u).ofLp i = u.ofLp i.succ := by
  rw [tailVec, WithLp.ofLp_toLp]

lemma contDiff_tailVec (k : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tailVec (k := k)) := by
  rw [contDiff_piLp (p := 2) (E := fun _ : Fin k => ℝ)]
  intro i
  rw [show (fun u : EuclideanSpace ℝ (Fin (k + 1)) => (tailVec u).ofLp i)
      = fun u : EuclideanSpace ℝ (Fin (k + 1)) => u.ofLp i.succ from
    funext (fun u => tailVec_ofLp u i)]
  exact contDiff_piLp_apply (p := 2) (E := fun _ : Fin (k + 1) => ℝ) (i := i.succ)

lemma contDiff_piLp_apply_zero {k : ℕ} :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin (k + 1)) => u.ofLp 0) :=
  contDiff_piLp_apply (p := 2) (E := fun _ : Fin (k + 1) => ℝ) (i := 0)

/-! ## The main smoothness theorem -/

/-- **The rotated presentation is smooth.**  For a `C^∞` nowhere-vanishing lift `V : ℝᵏ → ℝ⁴` of a
map into `ℝP³`, the rotated family `(t, x) ↦ projRot t [V x]` — written on the flattened parameter
space `ℝ^{k+1}` with `t` the first coordinate and `x` the tail — is `C^∞`. -/
theorem contMDiffAt_projRot_mk {k : ℕ} (V : EuclideanSpace ℝ (Fin k) → Eucl 3)
    (hV : ∀ x, V x ≠ 0) (u₀ : EuclideanSpace ℝ (Fin (k + 1)))
    (hVs : ContMDiffAt (𝓡 k) 𝓘(ℝ, Eucl 3) ((⊤ : ℕ∞) : WithTop ℕ∞) V (tailVec u₀)) :
    @ContMDiffAt ℝ _ (EuclideanSpace ℝ (Fin (k + 1))) _ _ (EuclideanSpace ℝ (Fin (k + 1))) _
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (EuclideanSpace ℝ (Fin (k + 1))) _ _
      (EuclideanSpace ℝ (Fin 3)) _ _ (EuclideanSpace ℝ (Fin 3)) _
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (Projectivization ℝ (Eucl 3)) _ (projCharted 3)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
        projRot (u.ofLp 0) (Projectivization.mk ℝ (V (tailVec u)) (hV (tailVec u)))) u₀ := by
  letI := projCharted 3
  have hWs : ContMDiffAt (𝓡 (k + 1)) 𝓘(ℝ, Eucl 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin (k + 1)) => diagRot (u.ofLp 0) (V (tailVec u))) u₀ := by
    rw [contMDiffAt_iff_contDiffAt]
    have ht : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : EuclideanSpace ℝ (Fin (k + 1)) => u.ofLp 0) u₀ :=
      contDiff_piLp_apply_zero.contDiffAt
    have hVt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : EuclideanSpace ℝ (Fin (k + 1)) => V (tailVec u)) u₀ :=
      hVs.contDiffAt.comp u₀ ((contDiff_tailVec k).contDiffAt)
    have hc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : EuclideanSpace ℝ (Fin (k + 1)) => circ (u.ofLp 0)) u₀ :=
      contDiff_circ.contDiffAt.comp u₀ ht
    have hs : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : EuclideanSpace ℝ (Fin (k + 1)) => star (circ (u.ofLp 0))) u₀ := by
      have h : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun u : EuclideanSpace ℝ (Fin (k + 1)) => circ (-(u.ofLp 0))) u₀ :=
        contDiff_circ.contDiffAt.comp u₀ ht.neg
      rwa [show (fun u : EuclideanSpace ℝ (Fin (k + 1)) => circ (-(u.ofLp 0)))
          = fun u => star (circ (u.ofLp 0)) from funext (fun u => circ_neg (u.ofLp 0))] at h
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : EuclideanSpace ℝ (Fin (k + 1)) => c₁ (V (tailVec u))) u₀ := by
      have h := (confProjVecOf_c₁CLM.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffAt.comp
        u₀ hVt
      simpa [Function.comp_def, confProjVecOf_c₁CLM_apply] using h
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : EuclideanSpace ℝ (Fin (k + 1)) => c₂ (V (tailVec u))) u₀ := by
      have h := (confProjVecOf_c₂CLM.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffAt.comp
        u₀ hVt
      simpa [Function.comp_def, confProjVecOf_c₂CLM_apply] using h
    show ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
        ofComplex (circ (u.ofLp 0) * c₁ (V (tailVec u)))
          (star (circ (u.ofLp 0)) * c₂ (V (tailVec u)))) u₀
    exact confProjVecOf_contDiffAt_ofComplex (hc.mul h1) (hs.mul h2)
  have h := contMDiffAt_projMk (n := 3) (k := k + 1)
    (fun u : EuclideanSpace ℝ (Fin (k + 1)) => diagRot (u.ofLp 0) (V (tailVec u)))
    (fun u => diagRot_ne_zero _ (hV _)) u₀ hWs
  have hfun : (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
        projRot (u.ofLp 0) (Projectivization.mk ℝ (V (tailVec u)) (hV (tailVec u))))
      = fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
          Projectivization.mk ℝ (diagRot (u.ofLp 0) (V (tailVec u)))
            (diagRot_ne_zero (u.ofLp 0) (hV (tailVec u))) := by
    funext u
    exact projRot_mk (u.ofLp 0) (V (tailVec u)) (hV (tailVec u))
  rw [hfun]
  exact h

/-! ## The product form of the smoothness theorem -/

/-- The flattening `(t, x) ↦ (t, x)` of a parameter pair into a single vector. -/
def flatVec {k : ℕ} (t : ℝ) (x : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin (k + 1)) :=
  WithLp.toLp 2 (Fin.cons t x.ofLp)

lemma flatVec_ofLp_zero {k : ℕ} (t : ℝ) (x : EuclideanSpace ℝ (Fin k)) :
    (flatVec t x).ofLp 0 = t := by
  rw [flatVec, WithLp.ofLp_toLp, Fin.cons_zero]

lemma flatVec_ofLp_succ {k : ℕ} (t : ℝ) (x : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    (flatVec t x).ofLp i.succ = x.ofLp i := by
  rw [flatVec, WithLp.ofLp_toLp, Fin.cons_succ]

lemma tailVec_flatVec {k : ℕ} (t : ℝ) (x : EuclideanSpace ℝ (Fin k)) :
    tailVec (flatVec t x) = x := by
  apply WithLp.ofLp_injective
  funext i
  rw [tailVec_ofLp, flatVec_ofLp_succ]

lemma contDiff_flatVec (k : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin k) => flatVec q.1 q.2) := by
  rw [contDiff_piLp (p := 2) (E := fun _ : Fin (k + 1) => ℝ)]
  intro j
  rw [show (fun q : ℝ × EuclideanSpace ℝ (Fin k) => (flatVec q.1 q.2).ofLp j)
      = fun q : ℝ × EuclideanSpace ℝ (Fin k) =>
          (Fin.cons q.1 q.2.ofLp : Fin (k + 1) → ℝ) j from
    funext (fun q => by rw [flatVec, WithLp.ofLp_toLp])]
  by_cases hj : j = 0
  · subst hj
    simp only [Fin.cons_zero]
    exact contDiff_fst
  · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj
    simp only [Fin.cons_succ]
    exact (contDiff_piLp_apply (p := 2) (E := fun _ : Fin k => ℝ) (i := i)).comp contDiff_snd

/-- **The rotated presentation is smooth (product form).**  For a `C^∞` nowhere-vanishing lift
`V : ℝᵏ → ℝ⁴` of a map into `ℝP³`, the rotated family `(t, x) ↦ projRot t [V x]` is `C^∞` on the
product `ℝ × ℝᵏ`. -/
theorem contMDiffAt_projRot_mk_prod {k : ℕ} (V : EuclideanSpace ℝ (Fin k) → Eucl 3)
    (hV : ∀ x, V x ≠ 0) (t₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin k))
    (hVs : ContMDiffAt (𝓡 k) 𝓘(ℝ, Eucl 3) ((⊤ : ℕ∞) : WithTop ℕ∞) V x₀) :
    (letI := projCharted 3
     ContMDiffAt (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin k)))
       (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
       (fun q : ℝ × EuclideanSpace ℝ (Fin k) =>
          projRot q.1 (Projectivization.mk ℝ (V q.2) (hV q.2))) (t₀, x₀)) := by
  letI := projCharted 3
  have hflat : ContMDiffAt (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin k)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin k) => flatVec q.1 q.2) (t₀, x₀) :=
    contMDiffAt_iff_contDiffAt.mpr ((contDiff_flatVec k).contDiffAt)
  have hVs' : ContMDiffAt (𝓡 k) 𝓘(ℝ, Eucl 3) ((⊤ : ℕ∞) : WithTop ℕ∞) V
      (tailVec (flatVec t₀ x₀)) := by
    rw [tailVec_flatVec]
    exact hVs
  have hmain := contMDiffAt_projRot_mk (k := k) V hV (flatVec t₀ x₀) hVs'
  have hcomp := hmain.comp (t₀, x₀) hflat
  have hfun : (fun q : ℝ × EuclideanSpace ℝ (Fin k) =>
        projRot ((flatVec q.1 q.2).ofLp 0)
          (Projectivization.mk ℝ (V (tailVec (flatVec q.1 q.2)))
            (hV (tailVec (flatVec q.1 q.2)))))
      = fun q : ℝ × EuclideanSpace ℝ (Fin k) =>
          projRot q.1 (Projectivization.mk ℝ (V q.2) (hV q.2)) := by
    funext q
    rw [flatVec_ofLp_zero, tailVec_flatVec]
  simp only [Function.comp_def] at hcomp
  rw [hfun] at hcomp
  exact hcomp

end

end Work.Drive
