import Mathlib
import Submission.Work.StemsB.SphHemi
import Submission.Work.Stems.SphereMinusPoint
import Submission.Work.RatHurewicz.SphereSuspDefs
import Submission.Work.RatHurewicz.subsingleton_zerothHomotopy_of_homotopyEquiv
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
import Submission.Work.Stems.sphereConnectivity

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-!
# The open cover of `S^{n+1}` used for Freudenthal's suspension theorem

This module sets up the open cover of `S^{n+1}` by

* `suspB n = {x : S^{n+1} | 0 < x_{n+1}}`, the open upper hemisphere, and
* `suspC n = {x : S^{n+1} | x ≠ N}`, the sphere with its north pole `N` removed,

together with what the Freudenthal argument needs about it: both pieces are contractible, both
carry a `Connector` (`suspB` through the explicit normalised chord `x ↦ (1-t)x + tN`, `suspC`
through the straight lines of the stereographic chart `Work.Stems.sphereComplHomeo`), and the
intersection `suspA n = suspB n ∩ suspC n = {0 < x_{n+1} ∧ x ≠ N}` is homeomorphic to
`Sⁿ × (0,1)`, with an explicit section/retraction pair `incl : Sⁿ → suspA`, `q : suspA → Sⁿ`,
`q (incl y) = y`.
-/

open scoped Topology unitInterval
open Metric

namespace Work.RatHurewicz

noncomputable section

/-! ## The cover -/

/-- The north pole of `S^{n+1}`. -/
def suspN (n : ℕ) : Sph (n + 1) := Work.StemsB.eLast (n + 1)

/-- The open upper hemisphere `{x : S^{n+1} | x_{n+1} > 0}`: the first piece of the cover. -/
def suspB (n : ℕ) : Set (Sph (n + 1)) := {x | 0 < lastC (n + 1) x}

/-- The sphere with its north pole removed: the second piece of the cover. -/
def suspC (n : ℕ) : Set (Sph (n + 1)) := {x | x ≠ suspN n}

/-- The intersection `suspB n ∩ suspC n = {x | 0 < x_{n+1} ∧ x ≠ N}`: the "punctured upper
hemisphere", which plays the role of the thickened equator. -/
def suspA (n : ℕ) : Set (Sph (n + 1)) := suspB n ∩ suspC n

theorem mem_suspB {n : ℕ} {x : Sph (n + 1)} : x ∈ suspB n ↔ 0 < lastC (n + 1) x := Iff.rfl

theorem mem_suspC {n : ℕ} {x : Sph (n + 1)} : x ∈ suspC n ↔ x ≠ suspN n := Iff.rfl

theorem mem_suspA {n : ℕ} {x : Sph (n + 1)} :
    x ∈ suspA n ↔ 0 < lastC (n + 1) x ∧ x ≠ suspN n := Iff.rfl

theorem isOpen_suspB (n : ℕ) : IsOpen (suspB n) :=
  isOpen_lt continuous_const ((continuous_lastC (n + 1)).comp continuous_subtype_val)

theorem isOpen_suspC (n : ℕ) : IsOpen (suspC n) := by
  have h : suspC n = ({suspN n} : Set (Sph (n + 1)))ᶜ := rfl
  rw [h]
  exact isOpen_compl_singleton

theorem lastC_suspN (n : ℕ) : lastC (n + 1) (suspN n) = 1 := by
  simp [suspN, lastC, Work.StemsB.eLast, Work.StemsB.npole_ofLp]

theorem suspB_union_suspC (n : ℕ) : suspB n ∪ suspC n = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, mem_suspB, mem_suspC, iff_true]
  by_cases h : x = suspN n
  · rw [h, lastC_suspN n]; norm_num
  · exact Or.inr h

/-! ## Coordinates and chords -/

theorem lastC_zero (m : ℕ) : lastC m (0 : EuclideanSpace ℝ (Fin (m + 1))) = 0 := by simp [lastC]

theorem lastC_add (m : ℕ) (a b : EuclideanSpace ℝ (Fin (m + 1))) :
    lastC m (a + b) = lastC m a + lastC m b := by simp [lastC]

theorem lastC_smul (m : ℕ) (c : ℝ) (a : EuclideanSpace ℝ (Fin (m + 1))) :
    lastC m (c • a) = c * lastC m a := by simp [lastC]

theorem lastC_npole (m : ℕ) : lastC m (Work.StemsB.npole m) = 1 := by
  simp [lastC, Work.StemsB.npole_ofLp]

theorem norm_eq_one_of_mem (m : ℕ) (x : Sph m) :
    ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 := by
  have h : (x : EuclideanSpace ℝ (Fin (m + 1))) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := x.2
  rw [Metric.mem_sphere, dist_zero_right] at h
  exact h

/-- The normalised straight line from `x` towards `y` in `ℝ^{m+1}`: for `x` and `y` on the sphere
this is the chord (a path in `S^m` from `x` to `y`). -/
def normChord (m : ℕ) (x y : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  (‖(1 - t) • x + t • y‖)⁻¹ • ((1 - t) • x + t • y)

theorem lastC_normChord (m : ℕ) (x y : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ) :
    lastC m (normChord m x y t) =
      (‖(1 - t) • x + t • y‖)⁻¹ * ((1 - t) * lastC m x + t * lastC m y) := by
  rw [normChord, lastC_smul, lastC_add, lastC_smul, lastC_smul]

theorem normChord_zero (m : ℕ) (x y : EuclideanSpace ℝ (Fin (m + 1))) :
    normChord m x y 0 = (‖x‖)⁻¹ • x := by
  simp only [normChord, sub_zero, one_smul, zero_smul, add_zero]

theorem normChord_one (m : ℕ) (x y : EuclideanSpace ℝ (Fin (m + 1))) :
    normChord m x y 1 = (‖y‖)⁻¹ • y := by
  simp only [normChord, sub_self, zero_smul, zero_add, one_smul]

theorem normChord_self (m : ℕ) (x y : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ) :
    normChord m x x t = (‖x‖)⁻¹ • x := by
  rw [normChord, ← add_smul, sub_add_cancel, one_smul]

theorem normChord_of_norm_one {m : ℕ} {x y : EuclideanSpace ℝ (Fin (m + 1))} (hx : ‖x‖ = 1) :
    normChord m x y 0 = x := by
  rw [normChord_zero, hx, inv_one, one_smul]

theorem normChord_one_of_norm_one {m : ℕ} {x y : EuclideanSpace ℝ (Fin (m + 1))}
    (hy : ‖y‖ = 1) : normChord m x y 1 = y := by
  rw [normChord_one, hy, inv_one, one_smul]

theorem normChord_self_of_norm_one {m : ℕ} {x : EuclideanSpace ℝ (Fin (m + 1))} (hx : ‖x‖ = 1)
    (t : ℝ) : normChord m x x t = x := by
  rw [normChord]
  have h : (1 - t) • x + t • x = x := by rw [← add_smul, sub_add_cancel, one_smul]
  rw [h, hx, inv_one, one_smul]

/-- A convex combination of two positive last coordinates is positive. -/
theorem lastC_chord_comb_pos (m : ℕ) (x y : EuclideanSpace ℝ (Fin (m + 1))) {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ 1) (hx : 0 < lastC m x) (hy : 0 < lastC m y) :
    0 < (1 - t) * lastC m x + t * lastC m y := by
  rcases lt_or_eq_of_le h1 with h | h
  · nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - t) hx, mul_nonneg h0 hy.le]
  · rw [h]; ring_nf; exact hy

theorem chord_ne_zero (m : ℕ) (x y : EuclideanSpace ℝ (Fin (m + 1))) {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ 1) (hx : 0 < lastC m x) (hy : 0 < lastC m y) :
    (1 - t) • x + t • y ≠ 0 := by
  intro h
  have h1' : lastC m ((1 - t) • x + t • y) = 0 := by rw [h, lastC_zero]
  rw [lastC_add, lastC_smul, lastC_smul] at h1'
  linarith [lastC_chord_comb_pos m x y h0 h1 hx hy]

/-- The normalised chord has norm one. -/
theorem norm_normChord (m : ℕ) (x y : EuclideanSpace ℝ (Fin (m + 1))) {t : ℝ}
    (ha : (1 - t) • x + t • y ≠ 0) : ‖normChord m x y t‖ = 1 := by
  rw [normChord, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)]

/-- The chord between two points of the upper hemisphere stays in the upper hemisphere. -/
theorem lastC_chord_pos (m : ℕ) (x y : EuclideanSpace ℝ (Fin (m + 1))) {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ 1) (hx : 0 < lastC m x) (hy : 0 < lastC m y) :
    0 < lastC m (normChord m x y t) := by
  rw [lastC_normChord]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (chord_ne_zero m x y h0 h1 hx hy)))
    (lastC_chord_comb_pos m x y h0 h1 hx hy)

/-! ## A connector gives contractibility -/

/-- **A space with a point and a connector is contractible.** -/
theorem contractibleSpace_of_connector {Y : Type*} [TopologicalSpace Y] (hc : Connector Y)
    (y₀ : Y) : ContractibleSpace Y := by
  rw [contractible_iff_id_nullhomotopic]
  have H : ContinuousMap.Homotopy (ContinuousMap.const Y y₀) (ContinuousMap.id Y) :=
    { toContinuousMap := ⟨fun p : I × Y => hc.c (y₀, p.2, p.1),
        hc.c.continuous.comp (continuous_const.prodMk
          (continuous_snd.prodMk continuous_fst))⟩
      map_zero_left := fun x => hc.zero y₀ x
      map_one_left := fun x => hc.one y₀ x }
  exact ⟨y₀, ⟨H.symm⟩⟩

/-! ## The upper hemisphere: chord connector and contractibility -/

theorem lastC_of_mem_suspB {n : ℕ} (p : ↥(suspB n)) :
    0 < lastC (n + 1) (p : EuclideanSpace ℝ (Fin (n + 2))) := p.2

/-- The normalised chord between two points of the upper hemisphere, as a point of the
hemisphere (the definition of the connector of `suspB`). -/
def suspBChord (n : ℕ) (p q : ↥(suspB n)) (t : I) : ↥(suspB n) :=
  ⟨⟨normChord (n + 1) (p : EuclideanSpace ℝ (Fin (n + 2)))
      (q : EuclideanSpace ℝ (Fin (n + 2))) (t : ℝ),
    (by
      show dist (normChord (n + 1) (p : EuclideanSpace ℝ (Fin (n + 2)))
          (q : EuclideanSpace ℝ (Fin (n + 2))) (t : ℝ)) 0 = 1
      rw [dist_zero_right]
      exact norm_normChord (n + 1) (p : EuclideanSpace ℝ (Fin (n + 2)))
        (q : EuclideanSpace ℝ (Fin (n + 2))) (t := (t : ℝ))
        (chord_ne_zero (n + 1) (p : EuclideanSpace ℝ (Fin (n + 2)))
          (q : EuclideanSpace ℝ (Fin (n + 2))) (t := (t : ℝ)) t.2.1 t.2.2
          (lastC_of_mem_suspB p) (lastC_of_mem_suspB q)))⟩,
    lastC_chord_pos (n + 1) (p : EuclideanSpace ℝ (Fin (n + 2)))
      (q : EuclideanSpace ℝ (Fin (n + 2))) (t := (t : ℝ)) t.2.1 t.2.2
      (lastC_of_mem_suspB p) (lastC_of_mem_suspB q)⟩

@[simp]
theorem suspBChord_coe (n : ℕ) (p q : ↥(suspB n)) (t : I) :
    ((suspBChord n p q t : ↥(suspB n)) : EuclideanSpace ℝ (Fin (n + 2))) =
      normChord (n + 1) (p : EuclideanSpace ℝ (Fin (n + 2)))
        (q : EuclideanSpace ℝ (Fin (n + 2))) (t : ℝ) := rfl

theorem continuous_suspBChord (n : ℕ) :
    Continuous fun p : ↥(suspB n) × ↥(suspB n) × I => suspBChord n p.1 p.2.1 p.2.2 := by
  have hchord : Continuous (fun p : ↥(suspB n) × ↥(suspB n) × I =>
      (1 - (p.2.2 : ℝ)) • (p.1 : EuclideanSpace ℝ (Fin (n + 2))) +
        (p.2.2 : ℝ) • (p.2.1 : EuclideanSpace ℝ (Fin (n + 2)))) := by fun_prop
  have hne : ∀ p : ↥(suspB n) × ↥(suspB n) × I,
      (1 - (p.2.2 : ℝ)) • (p.1 : EuclideanSpace ℝ (Fin (n + 2))) +
        (p.2.2 : ℝ) • (p.2.1 : EuclideanSpace ℝ (Fin (n + 2))) ≠ 0 :=
    fun p => chord_ne_zero (n + 1) _ _ (t := (p.2.2 : ℝ)) p.2.2.2.1 p.2.2.2.2
      (lastC_of_mem_suspB p.1) (lastC_of_mem_suspB p.2.1)
  have hinv : Continuous (fun p : ↥(suspB n) × ↥(suspB n) × I =>
      (‖(1 - (p.2.2 : ℝ)) • (p.1 : EuclideanSpace ℝ (Fin (n + 2))) +
        (p.2.2 : ℝ) • (p.2.1 : EuclideanSpace ℝ (Fin (n + 2)))‖)⁻¹) :=
    Continuous.inv₀ (continuous_norm.comp hchord) (fun p => norm_ne_zero_iff.mpr (hne p))
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact hinv.smul hchord

/-- The chord connector of the open upper hemisphere. -/
def suspBConn (n : ℕ) : Connector ↥(suspB n) where
  c := ⟨fun p : ↥(suspB n) × ↥(suspB n) × I => suspBChord n p.1 p.2.1 p.2.2,
    continuous_suspBChord n⟩
  zero := fun p q => by
    show suspBChord n p q 0 = p
    refine Subtype.ext (Subtype.ext ?_)
    rw [suspBChord_coe]
    exact normChord_of_norm_one (norm_eq_one_of_mem (n + 1) p)
  one := fun p q => by
    show suspBChord n p q 1 = q
    refine Subtype.ext (Subtype.ext ?_)
    rw [suspBChord_coe]
    exact normChord_one_of_norm_one (norm_eq_one_of_mem (n + 1) q)
  diag := fun p t => by
    show suspBChord n p p t = p
    refine Subtype.ext (Subtype.ext ?_)
    rw [suspBChord_coe]
    exact normChord_self_of_norm_one (norm_eq_one_of_mem (n + 1) p) (t : ℝ)

theorem suspB_contractible (n : ℕ) : ContractibleSpace ↥(suspB n) :=
  contractibleSpace_of_connector (suspBConn n)
    ⟨suspN n, by show 0 < lastC (n + 1) (suspN n); rw [lastC_suspN n]; norm_num⟩

/-! ## The sphere minus the north pole: chart connector and contractibility -/

/-- The chord connector of `S^{n+1}` with its north pole removed, obtained from the straight lines
of the stereographic chart `Work.Stems.sphereComplHomeo`. -/
def suspCConn (n : ℕ) : Connector ↥(suspC n) where
  c := ⟨fun p : ↥(suspC n) × ↥(suspC n) × I =>
      (Work.Stems.sphereComplHomeo (n + 1) (suspN n)).symm
        ((1 - (p.2.2 : ℝ)) • (Work.Stems.sphereComplHomeo (n + 1) (suspN n)) p.1 +
          (p.2.2 : ℝ) • (Work.Stems.sphereComplHomeo (n + 1) (suspN n)) p.2.1), by
    refine (Work.Stems.sphereComplHomeo (n + 1) (suspN n)).symm.continuous.comp ?_
    have hχ1 : Continuous (fun p : ↥(suspC n) × ↥(suspC n) × I =>
        (Work.Stems.sphereComplHomeo (n + 1) (suspN n)) p.1) :=
      (Work.Stems.sphereComplHomeo (n + 1) (suspN n)).continuous.comp continuous_fst
    have hχ2 : Continuous (fun p : ↥(suspC n) × ↥(suspC n) × I =>
        (Work.Stems.sphereComplHomeo (n + 1) (suspN n)) p.2.1) :=
      (Work.Stems.sphereComplHomeo (n + 1) (suspN n)).continuous.comp
        (continuous_fst.comp continuous_snd)
    have ht : Continuous (fun p : ↥(suspC n) × ↥(suspC n) × I => (p.2.2 : ℝ)) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    exact ((continuous_const.sub ht).smul hχ1).add (ht.smul hχ2)⟩
  zero := fun p q => by
    show (Work.Stems.sphereComplHomeo (n + 1) (suspN n)).symm
        ((1 - (0 : ℝ)) • (Work.Stems.sphereComplHomeo (n + 1) (suspN n)) p +
          (0 : ℝ) • (Work.Stems.sphereComplHomeo (n + 1) (suspN n)) q) = p
    rw [sub_zero, one_smul, zero_smul, add_zero]
    exact (Work.Stems.sphereComplHomeo (n + 1) (suspN n)).symm_apply_apply p
  one := fun p q => by
    show (Work.Stems.sphereComplHomeo (n + 1) (suspN n)).symm
        ((1 - (1 : ℝ)) • (Work.Stems.sphereComplHomeo (n + 1) (suspN n)) p +
          (1 : ℝ) • (Work.Stems.sphereComplHomeo (n + 1) (suspN n)) q) = q
    rw [sub_self, zero_smul, zero_add, one_smul]
    exact (Work.Stems.sphereComplHomeo (n + 1) (suspN n)).symm_apply_apply q
  diag := fun p t => by
    show (Work.Stems.sphereComplHomeo (n + 1) (suspN n)).symm
        ((1 - (t : ℝ)) • (Work.Stems.sphereComplHomeo (n + 1) (suspN n)) p +
          (t : ℝ) • (Work.Stems.sphereComplHomeo (n + 1) (suspN n)) p) = p
    rw [← add_smul, sub_add_cancel, one_smul]
    exact (Work.Stems.sphereComplHomeo (n + 1) (suspN n)).symm_apply_apply p

theorem suspC_contractible (n : ℕ) : ContractibleSpace ↥(suspC n) := by
  haveI hc : ContractibleSpace ↥(Set.univ :
      Set ((ℝ ∙ (suspN n : EuclideanSpace ℝ (Fin (n + 2))))ᗮ)) :=
    Convex.contractibleSpace convex_univ ⟨0, Set.mem_univ 0⟩
  haveI : ContractibleSpace ((ℝ ∙ (suspN n : EuclideanSpace ℝ (Fin (n + 2))))ᗮ) :=
    (Homeomorph.Set.univ _).symm.contractibleSpace
  exact (Work.Stems.sphereComplHomeo (n + 1) (suspN n)).contractibleSpace

/-! ## The tangential part and the last coordinate -/

/-- The **tangential part** of a vector of `ℝ^{n+2}`: its first `n+1` coordinates. -/
def tang (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 2))) : EuclideanSpace ℝ (Fin (n + 1)) :=
  (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm fun i => x.ofLp (Fin.castSucc i)

/-- The vector of `ℝ^{n+2}` with tangential part `v` and last coordinate `c`. -/
def snoc (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 1))) (c : ℝ) : EuclideanSpace ℝ (Fin (n + 2)) :=
  (WithLp.equiv 2 (Fin (n + 2) → ℝ)).symm (Fin.snoc (fun i : Fin (n + 1) => v.ofLp i) c)

@[simp]
theorem tang_ofLp (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 2))) (i : Fin (n + 1)) :
    (tang n x).ofLp i = x.ofLp (Fin.castSucc i) := by
  simp [tang]

@[simp]
theorem snoc_ofLp_castSucc (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 1))) (c : ℝ)
    (i : Fin (n + 1)) : (snoc n v c).ofLp (Fin.castSucc i) = v.ofLp i := by
  simp [snoc]

@[simp]
theorem snoc_ofLp_last (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 1))) (c : ℝ) :
    (snoc n v c).ofLp (Fin.last (n + 1)) = c := by
  simp [snoc]

@[simp]
theorem lastC_snoc (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 1))) (c : ℝ) :
    lastC (n + 1) (snoc n v c) = c := by
  simp [lastC]

@[simp]
theorem snoc_zero_one (n : ℕ) : snoc n 0 1 = Work.StemsB.npole (n + 1) := by
  refine PiLp.ext fun i => ?_
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;>
    simp [snoc, Work.StemsB.npole_ofLp]

@[simp]
theorem tang_snoc (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 1))) (c : ℝ) :
    tang n (snoc n v c) = v := by
  refine PiLp.ext fun i => ?_
  simp [tang, snoc]

theorem snoc_tang (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 2))) :
    snoc n (tang n x) (lastC (n + 1) x) = x := by
  refine PiLp.ext fun i => ?_
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp [snoc, tang]
  · simp [snoc, lastC]

theorem norm_sq_snoc (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 1))) (c : ℝ) :
    ‖snoc n v c‖ ^ 2 = ‖v‖ ^ 2 + c ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by simp
  · simp

theorem norm_sq_tang (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 2))) :
    ‖tang n x‖ ^ 2 = ‖x‖ ^ 2 - lastC (n + 1) x ^ 2 := by
  have h := norm_sq_snoc n (tang n x) (lastC (n + 1) x)
  rw [snoc_tang] at h
  linarith

theorem tang_ne_zero {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 2))) (hx : ‖x‖ = 1)
    (h0 : 0 < lastC (n + 1) x) (h1 : lastC (n + 1) x < 1) : tang n x ≠ 0 := by
  intro h
  have h2 : ‖tang n x‖ ^ 2 = 0 := by rw [h]; simp
  rw [norm_sq_tang, hx] at h2
  nlinarith [sq_nonneg (lastC (n + 1) x)]

theorem tang_add (n : ℕ) (a b : EuclideanSpace ℝ (Fin (n + 2))) :
    tang n (a + b) = tang n a + tang n b := by
  refine PiLp.ext fun i => ?_
  simp [tang, PiLp.add_apply]

theorem tang_smul (n : ℕ) (c : ℝ) (a : EuclideanSpace ℝ (Fin (n + 2))) :
    tang n (c • a) = c • tang n a := by
  refine PiLp.ext fun i => ?_
  simp [tang, PiLp.smul_apply]

theorem snoc_add (n : ℕ) (a b : EuclideanSpace ℝ (Fin (n + 1)) × ℝ) :
    snoc n (a.1 + b.1) (a.2 + b.2) = snoc n a.1 a.2 + snoc n b.1 b.2 := by
  refine PiLp.ext fun i => ?_
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;> simp [snoc, PiLp.add_apply]

theorem snoc_smul (n : ℕ) (c : ℝ) (a : EuclideanSpace ℝ (Fin (n + 1)) × ℝ) :
    snoc n (c • a.1) (c * a.2) = c • snoc n a.1 a.2 := by
  refine PiLp.ext fun i => ?_
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;> simp [snoc, PiLp.smul_apply]

/-- The tangential part, as a linear map. -/
def tangLM (n : ℕ) : EuclideanSpace ℝ (Fin (n + 2)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) where
  toFun := tang n
  map_add' := tang_add n
  map_smul' := tang_smul n

/-- The insertion of a last coordinate, as a linear map. -/
def snocLM (n : ℕ) :
    (EuclideanSpace ℝ (Fin (n + 1)) × ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 2)) where
  toFun p := snoc n p.1 p.2
  map_add' := snoc_add n
  map_smul' := snoc_smul n

theorem continuous_tang (n : ℕ) : Continuous (tang n) :=
  (tangLM n).continuous_of_finiteDimensional

theorem continuous_snoc (n : ℕ) :
    Continuous fun p : EuclideanSpace ℝ (Fin (n + 1)) × ℝ => snoc n p.1 p.2 :=
  (snocLM n).continuous_of_finiteDimensional

/-- The last coordinate of a point of `suspA` is strictly less than one. -/
theorem lastC_lt_one_of_suspA {n : ℕ} (x : ↥(suspA n)) :
    lastC (n + 1) (x : EuclideanSpace ℝ (Fin (n + 2))) < 1 := by
  rcases lt_or_ge (lastC (n + 1) (x : EuclideanSpace ℝ (Fin (n + 2)))) 1 with h | h
  · exact h
  · exfalso
    have hle : lastC (n + 1) (x : EuclideanSpace ℝ (Fin (n + 2))) ≤ 1 := by
      have h2 := norm_sq_tang n (x : EuclideanSpace ℝ (Fin (n + 2)))
      rw [norm_eq_one_of_mem (n + 1) x.1] at h2
      nlinarith [sq_nonneg (lastC (n + 1) (x : EuclideanSpace ℝ (Fin (n + 2))))]
    have heq : lastC (n + 1) (x : EuclideanSpace ℝ (Fin (n + 2))) = 1 := le_antisymm hle h
    have ht : tang n (x : EuclideanSpace ℝ (Fin (n + 2))) = 0 := by
      have h2 : ‖tang n (x : EuclideanSpace ℝ (Fin (n + 2)))‖ ^ 2 = 0 := by
        rw [norm_sq_tang, norm_eq_one_of_mem (n + 1) x.1, heq]; norm_num
      have h3 : ‖tang n (x : EuclideanSpace ℝ (Fin (n + 2)))‖ = 0 := by
        nlinarith [norm_nonneg (tang n (x : EuclideanSpace ℝ (Fin (n + 2))))]
      rwa [norm_eq_zero] at h3
    refine x.2.2 (Subtype.ext ?_)
    rw [← snoc_tang n (x : EuclideanSpace ℝ (Fin (n + 2))), heq, ht, snoc_zero_one]
    rfl

/-- **The projection `suspA → Sⁿ`**: the normalisation of the tangential part. -/
def suspAProj (n : ℕ) : C(↥(suspA n), Sph n) where
  toFun x := ⟨(‖tang n (x : EuclideanSpace ℝ (Fin (n + 2)))‖)⁻¹ •
      tang n (x : EuclideanSpace ℝ (Fin (n + 2))), by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (tang_ne_zero _
        (norm_eq_one_of_mem (n + 1) x.1) x.2.1 (lastC_lt_one_of_suspA x)))]⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have hval : Continuous fun x : ↥(suspA n) => ((x : Sph (n + 1)) :
        EuclideanSpace ℝ (Fin (n + 2))) :=
      continuous_subtype_val.comp (continuous_subtype_val :
        Continuous fun x : ↥(suspA n) => (x.1 : Sph (n + 1)))
    have ht : Continuous fun x : ↥(suspA n) =>
        tang n (x : EuclideanSpace ℝ (Fin (n + 2))) :=
      (continuous_tang n).comp hval
    have hinv : Continuous fun x : ↥(suspA n) =>
        (‖tang n (x : EuclideanSpace ℝ (Fin (n + 2)))‖)⁻¹ :=
      Continuous.inv₀ (continuous_norm.comp ht) fun x => norm_ne_zero_iff.mpr
        (tang_ne_zero _ (norm_eq_one_of_mem (n + 1) x.1) x.2.1 (lastC_lt_one_of_suspA x))
    exact hinv.smul ht

/-! ## The section `Sⁿ → suspA`, the projection, and the deformation -/

theorem suspAProj_val (n : ℕ) (x : ↥(suspA n)) :
    (suspAProj n x : EuclideanSpace ℝ (Fin (n + 1))) =
      (‖tang n (x : EuclideanSpace ℝ (Fin (n + 2)))‖)⁻¹ •
        tang n (x : EuclideanSpace ℝ (Fin (n + 2))) := rfl

theorem suspAProj_norm (n : ℕ) (x : ↥(suspA n)) :
    ‖(suspAProj n x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 :=
  norm_eq_one_of_mem n (suspAProj n x)

/-- The last coordinate used along the deformation of `suspA` onto the equator of `Sⁿ`. -/
def suspAVar (n : ℕ) (x : ↥(suspA n)) (τ : I) : ℝ :=
  (1 - (τ : ℝ)) * (1 / 2) + (τ : ℝ) * lastC (n + 1) (x : EuclideanSpace ℝ (Fin (n + 2)))

theorem continuous_suspA_val (n : ℕ) : Continuous fun x : ↥(suspA n) =>
    (x : EuclideanSpace ℝ (Fin (n + 2))) :=
  continuous_subtype_val.comp (continuous_subtype_val :
    Continuous fun x : ↥(suspA n) => (x.1 : Sph (n + 1)))

theorem continuous_suspAVar (n : ℕ) :
    Continuous fun p : ↥(suspA n) × I => suspAVar n p.1 p.2 := by
  refine Continuous.add ?_ ?_
  · exact (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul continuous_const
  · exact (continuous_subtype_val.comp continuous_snd).mul
      ((continuous_lastC (n + 1)).comp ((continuous_suspA_val n).comp continuous_fst))

theorem suspAVar_pos (n : ℕ) (x : ↥(suspA n)) (τ : I) : 0 < suspAVar n x τ := by
  rcases lt_or_eq_of_le τ.2.2 with h | h
  · have h1 : 0 < 1 - (τ : ℝ) := by linarith
    have : 0 < (1 - (τ : ℝ)) * (1 / 2) := by linarith
    have h2 : 0 ≤ (τ : ℝ) * lastC (n + 1) (x : EuclideanSpace ℝ (Fin (n + 2))) :=
      mul_nonneg τ.2.1 x.2.1.le
    rw [suspAVar]; linarith
  · rw [suspAVar, h]; ring_nf; exact x.2.1

theorem suspAVar_lt_one (n : ℕ) (x : ↥(suspA n)) (τ : I) : suspAVar n x τ < 1 := by
  have hs := lastC_lt_one_of_suspA x
  rcases lt_or_eq_of_le τ.2.2 with h | h
  · have h1 : 0 < 1 - (τ : ℝ) := by linarith
    have h2 : (τ : ℝ) * lastC (n + 1) (x : EuclideanSpace ℝ (Fin (n + 2))) ≤ (τ : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hs.le τ.2.1
    have h3 : (1 - (τ : ℝ)) * (1 / 2) < (1 - (τ : ℝ)) * 1 := by linarith
    rw [suspAVar]; nlinarith
  · rw [suspAVar, h]; ring_nf; exact hs

theorem suspendVar_sq_le_one (n : ℕ) (x : ↥(suspA n)) (τ : I) :
    1 - suspAVar n x τ ^ 2 ≥ 0 := by
  have h0 := suspAVar_pos n x τ
  have h1 := suspAVar_lt_one n x τ
  nlinarith

theorem ne_suspN_of_lastC_ne_one {n : ℕ} {y : Sph (n + 1)}
    (h : lastC (n + 1) (y : EuclideanSpace ℝ (Fin (n + 2))) ≠ 1) : y ≠ suspN n := by
  intro hc
  exact h (by rw [hc, lastC_suspN])

/-- The deformation of `suspA` onto its projection (the underlying bound map). -/
def suspAHomotopyFun (n : ℕ) (p : ↥(suspA n) × I) : ↥(suspA n) := by
  have hsq : 1 - suspAVar n p.1 p.2 ^ 2 ≥ 0 := suspendVar_sq_le_one n p.1 p.2
  have hnorm : ‖snoc n (Real.sqrt (1 - suspAVar n p.1 p.2 ^ 2) •
      (suspAProj n p.1 : EuclideanSpace ℝ (Fin (n + 1)))) (suspAVar n p.1 p.2)‖ = 1 := by
    have h2 : ‖snoc n (Real.sqrt (1 - suspAVar n p.1 p.2 ^ 2) •
        (suspAProj n p.1 : EuclideanSpace ℝ (Fin (n + 1)))) (suspAVar n p.1 p.2)‖ ^ 2 = 1 := by
      rw [norm_sq_snoc, norm_smul, suspAProj_norm n p.1, mul_one, Real.norm_eq_abs, sq_abs,
        Real.sq_sqrt hsq]
      ring
    nlinarith [norm_nonneg (snoc n (Real.sqrt (1 - suspAVar n p.1 p.2 ^ 2) •
      (suspAProj n p.1 : EuclideanSpace ℝ (Fin (n + 1)))) (suspAVar n p.1 p.2))]
  let v : Sph (n + 1) := ⟨snoc n (Real.sqrt (1 - suspAVar n p.1 p.2 ^ 2) •
      (suspAProj n p.1 : EuclideanSpace ℝ (Fin (n + 1)))) (suspAVar n p.1 p.2), by
    rw [Metric.mem_sphere, dist_zero_right]; exact hnorm⟩
  have hmemB : v ∈ suspB n := by
    show 0 < lastC (n + 1) (v : EuclideanSpace ℝ (Fin (n + 2)))
    rw [show ((v : Sph (n + 1)) : EuclideanSpace ℝ (Fin (n + 2))) = snoc n
        (Real.sqrt (1 - suspAVar n p.1 p.2 ^ 2) •
          (suspAProj n p.1 : EuclideanSpace ℝ (Fin (n + 1)))) (suspAVar n p.1 p.2) from rfl]
    rw [lastC_snoc]
    exact suspAVar_pos n p.1 p.2
  have hmemC : v ∈ suspC n := by
    refine ne_suspN_of_lastC_ne_one ?_
    rw [show ((v : Sph (n + 1)) : EuclideanSpace ℝ (Fin (n + 2))) = snoc n
        (Real.sqrt (1 - suspAVar n p.1 p.2 ^ 2) •
          (suspAProj n p.1 : EuclideanSpace ℝ (Fin (n + 1)))) (suspAVar n p.1 p.2) from rfl]
    rw [lastC_snoc]
    exact ne_of_lt (suspAVar_lt_one n p.1 p.2)
  exact ⟨v, hmemB, hmemC⟩

theorem continuous_suspAHomotopyVal (n : ℕ) : Continuous fun p : ↥(suspA n) × I =>
    snoc n (Real.sqrt (1 - suspAVar n p.1 p.2 ^ 2) •
      (suspAProj n p.1 : EuclideanSpace ℝ (Fin (n + 1)))) (suspAVar n p.1 p.2) := by
  have h1 : Continuous fun p : ↥(suspA n) × I => suspAVar n p.1 p.2 := continuous_suspAVar n
  have h2 : Continuous fun p : ↥(suspA n) × I =>
      (suspAProj n p.1 : EuclideanSpace ℝ (Fin (n + 1))) :=
    ((continuous_subtype_val : Continuous fun z : Sph n =>
        (z : EuclideanSpace ℝ (Fin (n + 1)))).comp
      ((suspAProj n).continuous.comp (continuous_fst :
        Continuous fun p : ↥(suspA n) × I => p.1)))
  have h3 : Continuous fun p : ↥(suspA n) × I =>
      Real.sqrt (1 - suspAVar n p.1 p.2 ^ 2) :=
    Real.continuous_sqrt.comp (continuous_const.sub (h1.pow 2))
  have h4 : Continuous fun p : ↥(suspA n) × I =>
      Real.sqrt (1 - suspAVar n p.1 p.2 ^ 2) •
        (suspAProj n p.1 : EuclideanSpace ℝ (Fin (n + 1))) := h3.smul h2
  exact (continuous_snoc n).comp (Continuous.prodMk h4 h1)

theorem continuous_suspAHomotopyFun (n : ℕ) : Continuous (suspAHomotopyFun n) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact continuous_suspAHomotopyVal n

/-! ## The section `Sⁿ → suspA` -/

/-- The last coordinate used in the section `Sⁿ → suspA`. -/
def suspAC : ℝ := Real.sqrt (1 - (1 / 2 : ℝ) ^ 2)

theorem suspAC_pos : 0 < suspAC := by
  rw [suspAC]
  apply Real.sqrt_pos.mpr
  norm_num

theorem suspAC_sq : suspAC ^ 2 = 1 - (1 / 2 : ℝ) ^ 2 := by
  rw [suspAC, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1 - (1 / 2 : ℝ) ^ 2)]

/-- The section `Sⁿ → suspA`: the point with tangential part `suspAC • y` and last coordinate
`1/2`. -/
def suspAInclFun (n : ℕ) (y : Sph n) : ↥(suspA n) := by
  have hnorm : ‖snoc n (suspAC • (y : EuclideanSpace ℝ (Fin (n + 1)))) (1 / 2 : ℝ)‖ = 1 := by
    have h2 : ‖snoc n (suspAC • (y : EuclideanSpace ℝ (Fin (n + 1)))) (1 / 2 : ℝ)‖ ^ 2 = 1 := by
      rw [norm_sq_snoc, norm_smul, norm_eq_one_of_mem n y, mul_one, Real.norm_eq_abs, sq_abs,
        suspAC_sq]
      norm_num
    nlinarith [norm_nonneg (snoc n (suspAC • (y : EuclideanSpace ℝ (Fin (n + 1)))) (1 / 2 : ℝ))]
  let v : Sph (n + 1) := ⟨snoc n (suspAC • (y : EuclideanSpace ℝ (Fin (n + 1)))) (1 / 2 : ℝ), by
    rw [Metric.mem_sphere, dist_zero_right]; exact hnorm⟩
  have hmemB : v ∈ suspB n := by
    show 0 < lastC (n + 1) (v : EuclideanSpace ℝ (Fin (n + 2)))
    rw [show ((v : Sph (n + 1)) : EuclideanSpace ℝ (Fin (n + 2))) = snoc n
      (suspAC • (y : EuclideanSpace ℝ (Fin (n + 1)))) (1 / 2 : ℝ) from rfl, lastC_snoc]
    norm_num
  have hmemC : v ∈ suspC n := by
    refine ne_suspN_of_lastC_ne_one ?_
    rw [show ((v : Sph (n + 1)) : EuclideanSpace ℝ (Fin (n + 2))) = snoc n
      (suspAC • (y : EuclideanSpace ℝ (Fin (n + 1)))) (1 / 2 : ℝ) from rfl, lastC_snoc]
    norm_num
  exact ⟨v, hmemB, hmemC⟩

/-- The section `Sⁿ → suspA`, as a continuous map. -/
def suspAIncl (n : ℕ) : C(Sph n, ↥(suspA n)) where
  toFun := suspAInclFun n
  continuous_toFun := by
    have hval : Continuous fun y : Sph n => (y : EuclideanSpace ℝ (Fin (n + 1))) :=
      (continuous_subtype_val : Continuous fun y : Sph n =>
        (y : EuclideanSpace ℝ (Fin (n + 1))))
    have h : Continuous fun y : Sph n =>
        snoc n (suspAC • (y : EuclideanSpace ℝ (Fin (n + 1)))) (1 / 2 : ℝ) :=
      (continuous_snoc n).comp (Continuous.prodMk
        ((continuous_const : Continuous fun _ : Sph n => suspAC).smul hval) continuous_const)
    exact Continuous.subtype_mk (Continuous.subtype_mk h _) _

/-! ## The projection is a retraction of the section, and `suspA` is `(n-1)`-connected -/

@[simp]
theorem suspAHomotopyFun_val (n : ℕ) (p : ↥(suspA n) × I) :
    ((suspAHomotopyFun n p : ↥(suspA n)) : EuclideanSpace ℝ (Fin (n + 2))) =
      snoc n (Real.sqrt (1 - suspAVar n p.1 p.2 ^ 2) •
        (suspAProj n p.1 : EuclideanSpace ℝ (Fin (n + 1)))) (suspAVar n p.1 p.2) := rfl

@[simp]
theorem suspAIncl_val (n : ℕ) (y : Sph n) :
    ((suspAIncl n y : ↥(suspA n)) : EuclideanSpace ℝ (Fin (n + 2))) =
      snoc n (suspAC • (y : EuclideanSpace ℝ (Fin (n + 1)))) (1 / 2) := rfl

@[simp]
theorem suspAVar_zero (n : ℕ) (x : ↥(suspA n)) : suspAVar n x 0 = 1 / 2 := by
  simp [suspAVar]

@[simp]
theorem suspAVar_one (n : ℕ) (x : ↥(suspA n)) :
    suspAVar n x 1 = lastC (n + 1) (x : EuclideanSpace ℝ (Fin (n + 2))) := by
  simp [suspAVar]

theorem tang_suspAIncl (n : ℕ) (y : Sph n) :
    tang n ((suspAIncl n y : ↥(suspA n)) : EuclideanSpace ℝ (Fin (n + 2))) =
      suspAC • (y : EuclideanSpace ℝ (Fin (n + 1))) := by
  rw [suspAIncl_val, tang_snoc]

/-- The projection is a left inverse of the section. -/
theorem suspAProj_incl (n : ℕ) (y : Sph n) : suspAProj n (suspAIncl n y) = y := by
  apply Subtype.ext
  show (suspAProj n (suspAIncl n y) : EuclideanSpace ℝ (Fin (n + 1))) =
    (y : EuclideanSpace ℝ (Fin (n + 1)))
  rw [suspAProj_val, tang_suspAIncl, norm_smul, norm_eq_one_of_mem n y, mul_one,
    Real.norm_eq_abs, abs_of_pos suspAC_pos, smul_smul,
    inv_mul_cancel₀ (ne_of_gt suspAC_pos), one_smul]

theorem sqrt_one_sub_sq_eq_norm_tang {n : ℕ} (x : ↥(suspA n)) :
    Real.sqrt (1 - lastC (n + 1) (x : EuclideanSpace ℝ (Fin (n + 2))) ^ 2) =
      ‖tang n (x : EuclideanSpace ℝ (Fin (n + 2)))‖ := by
  have h := norm_sq_tang n (x : EuclideanSpace ℝ (Fin (n + 2)))
  rw [norm_eq_one_of_mem (n + 1) x.1] at h
  have hsq : (Real.sqrt (1 - lastC (n + 1) (x : EuclideanSpace ℝ (Fin (n + 2))) ^ 2)) ^ 2 =
      ‖tang n (x : EuclideanSpace ℝ (Fin (n + 2)))‖ ^ 2 := by
    rw [Real.sq_sqrt (by nlinarith [h, sq_nonneg (‖tang n (x : EuclideanSpace ℝ (Fin (n + 2)))‖)])]
    linarith [h]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h' | h'
  · exact h'
  · have h1 : (0:ℝ) ≤ Real.sqrt
        (1 - lastC (n + 1) (x : EuclideanSpace ℝ (Fin (n + 2))) ^ 2) := Real.sqrt_nonneg _
    have h2 : (0:ℝ) ≤ ‖tang n (x : EuclideanSpace ℝ (Fin (n + 2)))‖ := norm_nonneg _
    linarith

theorem suspAHomotopyFun_zero (n : ℕ) (x : ↥(suspA n)) :
    suspAHomotopyFun n (x, 0) = suspAIncl n (suspAProj n x) := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [suspAHomotopyFun_val, suspAIncl_val, suspAVar_zero]
  rfl

theorem suspAHomotopyFun_one_val (n : ℕ) (x : ↥(suspA n)) :
    snoc n (Real.sqrt (1 - suspAVar n x 1 ^ 2) •
        (suspAProj n x : EuclideanSpace ℝ (Fin (n + 1)))) (suspAVar n x 1) =
      (x : EuclideanSpace ℝ (Fin (n + 2))) := by
  rw [suspAVar_one, sqrt_one_sub_sq_eq_norm_tang x, suspAProj_val, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr (tang_ne_zero _
      (norm_eq_one_of_mem (n + 1) x.1) x.2.1 (lastC_lt_one_of_suspA x))), one_smul]
  exact snoc_tang n (x : EuclideanSpace ℝ (Fin (n + 2)))

theorem suspAHomotopyFun_one (n : ℕ) (x : ↥(suspA n)) : suspAHomotopyFun n (x, 1) = x := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [suspAHomotopyFun_val]
  exact suspAHomotopyFun_one_val n x

/-- The deformation retraction of `suspA` onto the section of its projection. -/
def suspAHomotopy (n : ℕ) :
    ContinuousMap.Homotopy ((suspAIncl n).comp (suspAProj n)) (ContinuousMap.id ↥(suspA n)) where
  toContinuousMap := {
    toFun := fun q : I × ↥(suspA n) => suspAHomotopyFun n (q.2, q.1)
    continuous_toFun := (continuous_suspAHomotopyFun n).comp
      (continuous_snd.prodMk continuous_fst) }
  map_zero_left := fun x => suspAHomotopyFun_zero n x
  map_one_left := fun x => suspAHomotopyFun_one n x

/-- **`suspA n` is homotopy equivalent to `Sⁿ`.** -/
def suspAHomotopyEquiv (n : ℕ) : ContinuousMap.HomotopyEquiv ↥(suspA n) (Sph n) where
  toFun := suspAProj n
  invFun := suspAIncl n
  left_inv := ⟨suspAHomotopy n⟩
  right_inv := by
    have h : (suspAProj n).comp (suspAIncl n) = ContinuousMap.id (Sph n) :=
      ContinuousMap.ext (suspAProj_incl n)
    rw [h]

/-- **The thickened equator `suspA n` is `(n-1)`-connected.** -/
theorem subsingleton_homotopyGroup_suspA (n e : ℕ) (he : e < n) (z : ↥(suspA n)) :
    Subsingleton (HomotopyGroup (Fin e) ↥(suspA n) z) := by
  rcases Nat.eq_zero_or_pos e with h0 | hpos
  · subst h0
    have hne : Nonempty (Sph n) := ⟨Work.StemsB.eLast n⟩
    let e1 := HomotopyGroup.pi0EquivZerothHomotopy (X := Sph n) (x := Classical.choice hne)
    have hpi0 : Subsingleton (HomotopyGroup (Fin 0) (Sph n) (Classical.choice hne)) :=
      Work.Stems.sphereConnectivity n 0 he (Classical.choice hne)
    have hZ : Subsingleton (ZerothHomotopy (Sph n)) :=
      ⟨fun a b => e1.symm.injective (hpi0.allEq (e1.symm a) (e1.symm b))⟩
    have hZA : Subsingleton (ZerothHomotopy ↥(suspA n)) :=
      subsingleton_zerothHomotopy_of_homotopyEquiv (suspAHomotopyEquiv n) hZ
    refine ⟨fun a b => ?_⟩
    exact (HomotopyGroup.pi0EquivZerothHomotopy (X := ↥(suspA n)) (x := z)).injective
      (hZA.allEq _ _)
  · obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    obtain ⟨me⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin (e' + 1))
      (suspAHomotopyEquiv n) z
    have hsphere : Subsingleton
        (HomotopyGroup (Fin (e' + 1)) (Sph n) ((suspAHomotopyEquiv n).toFun z)) :=
      Work.Stems.sphereConnectivity n (e' + 1) (by omega) ((suspAHomotopyEquiv n).toFun z)
    refine ⟨fun a b => ?_⟩
    exact me.injective (hsphere.allEq (me a) (me b))

end

end Work.RatHurewicz
