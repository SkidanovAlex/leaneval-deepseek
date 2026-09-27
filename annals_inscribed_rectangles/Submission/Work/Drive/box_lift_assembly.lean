import Mathlib
import Submission.Work.Drive.projCharted
import Submission.Work.Drive.ProjectiveTopology
import Submission.Work.Drive.ProjectiveChartDefs
import Submission.Work.Drive.exists_contDiff_extension_box
import Submission.Work.Drive.exists_contDiff_flattening
import Submission.Work.Drive.exists_localModel_projCharted
import Submission.Work.Drive.isCoveringMap_projOfUnitSphere
import Submission.Work.Drive.exists_local_unit_lift_projCharted
import Submission.Work.Drive.exists_lift_box_projOfUnitSphere
import Submission.Work.Drive.lift_eq_or_neg_of_isPreconnected

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Filter

noncomputable section

/-!
# A global smooth nonvanishing lift of a `C^∞`-on-a-box map into `ℝP³`

`Work.Drive.box_lift_assembly` (the target of this file)  produces, from a map
`h : ℝ² → ℝP³` that is `C^∞` (Whitney) on a closed box `[a,b] × [c,d]`, a *globally* `C^∞`
and nowhere vanishing `V : ℝ² → ℝ⁴` whose projective class reproduces `h` on the box.

The proof assembles four independent pieces:

* `Work.Drive.exists_lift_box_projOfUnitSphere` — a continuous unit lift `v : ℝ² → S³` of `h` on
  the box (the box is convex, hence simply connected, so the covering map `S³ → ℝP³` lifts);
* `Work.Drive.exists_local_unit_lift_projCharted` — near every box point, a *smooth* unit lift
  `u : ℝ² → S³` of `h` on the box, defined on the whole plane;
* `Work.Drive.lift_eq_or_neg_of_isPreconnected` — the two lifts agree on the (preconnected) part
  of the box near that point, up to a *constant* sign; this turns the local lifts into genuine
  local pieces for the continuous lift `v`;
* `glue_local_pieces_box` below — local-to-global glueing (a partition of unity) producing a
  global `C^∞` map `G` agreeing with `v` on the box.

Then `G` is nonvanishing on a neighbourhood of the box (it equals the unit vector `v` there) and
`flattening_into_nhd` produces a smooth retraction `φ` of the plane into that neighbourhood;
`V := G ∘ φ` is the required lift.
-/

/-! ## The box in `ℝ²` -/

/-- The closed box `[a,b] × [c,d]` in `ℝ²`. -/
def boxE (a b c d : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {q | q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d}

lemma convex_boxE (a b c d : ℝ) : Convex ℝ (boxE a b c d) := by
  intro x hx y hy p q hp hq hpq
  refine ⟨?_, ?_⟩
  · have h := convex_Icc a b hx.1 hy.1 hp hq hpq
    simpa [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using h
  · have h := convex_Icc c d hx.2 hy.2 hp hq hpq
    simpa [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using h

lemma boxE_isCompact (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    IsCompact (boxE a b c d) := by
  have hclosed : IsClosed (boxE a b c d) := by
    have h1 : IsClosed {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a b} :=
      isClosed_Icc.preimage (by fun_prop)
    have h2 : IsClosed {q : EuclideanSpace ℝ (Fin 2) | q 1 ∈ Set.Icc c d} :=
      isClosed_Icc.preimage (by fun_prop)
    have h12 : IsClosed ({q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a b} ∩
        {q : EuclideanSpace ℝ (Fin 2) | q 1 ∈ Set.Icc c d}) := h1.inter h2
    convert h12 using 1
    ext q
    simp [boxE]
  have hbdd : Bornology.IsBounded (boxE a b c d) := by
    refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin 2)))
      (r := |a| + |b| + |c| + |d| + 1)).subset ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    have h0 : |x 0| ≤ |a| + |b| := by
      rcases le_total 0 (x 0) with h | h
      · rw [abs_of_nonneg h]; linarith [le_abs_self b, abs_nonneg a, hx.1.2]
      · rw [abs_of_nonpos h]; linarith [neg_abs_le a, abs_nonneg b, hx.1.1]
    have h1 : |x 1| ≤ |c| + |d| := by
      rcases le_total 0 (x 1) with h | h
      · rw [abs_of_nonneg h]; linarith [le_abs_self d, abs_nonneg c, hx.2.2]
      · rw [abs_of_nonpos h]; linarith [neg_abs_le c, abs_nonneg d, hx.2.1]
    have h2 : ‖x‖ ≤ |x 0| + |x 1| := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      nlinarith [sq_abs (x 0), sq_abs (x 1), abs_nonneg (x 0), abs_nonneg (x 1),
        sq_nonneg (|x 0| + |x 1|)]
    linarith [abs_nonneg a, abs_nonneg b, abs_nonneg c, abs_nonneg d]
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbdd⟩

/-! ## Two elementary facts about projective classes -/

/-- Equal non-zero vectors define the same projective point (the non-vanishing proofs are
irrelevant). -/
lemma mk_eq_mk_of_eq {u w : EuclideanSpace ℝ (Fin 4)} (h : u = w) (hu : u ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk ℝ u hu = Projectivization.mk ℝ w hw := by
  subst h
  exact projectivizationMk_congr ℝ _

/-- The projective class of a point of the unit sphere is `projOfUnitSphere`. -/
lemma mk_coe_eq_projOfUnitSphere (v : unitSphere 3)
    (hne : (v : EuclideanSpace ℝ (Fin 4)) ≠ 0) :
    Projectivization.mk ℝ (v : EuclideanSpace ℝ (Fin 4)) hne = projOfUnitSphere v := by
  rw [projOfUnitSphere_eq, projOfUnit_eq_mk]

/-! ## Local-to-global glueing on the box -/

/-- **Local-to-global glueing.**  If every point `p` of the box `[a,b] × [c,d]` has a `C^∞` map
`g_p : ℝ² → E` agreeing with `u` on the part of the box inside `ball p (r_p)`, then the restriction
of `u` to the box is the restriction of a globally `C^∞` map. -/
lemma glue_local_pieces_box (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : EuclideanSpace ℝ (Fin 2) → E}
    (h : ∀ p : EuclideanSpace ℝ (Fin 2), p 0 ∈ Set.Icc a b → p 1 ∈ Set.Icc c d →
      ∃ r : ℝ, 0 < r ∧ ∃ g : EuclideanSpace ℝ (Fin 2) → E,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
        ∀ x : EuclideanSpace ℝ (Fin 2), x 0 ∈ Set.Icc a b → x 1 ∈ Set.Icc c d →
          dist x p < r → g x = u x) :
    ∃ g : EuclideanSpace ℝ (Fin 2) → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ x : EuclideanSpace ℝ (Fin 2), x 0 ∈ Set.Icc a b → x 1 ∈ Set.Icc c d → g x = u x := by
  classical
  have hK : IsCompact (boxE a b c d) := boxE_isCompact a b c d hab hcd
  choose r hr g hg using fun p : boxE a b c d => h p.1 p.2.1 p.2.2
  have hcov : boxE a b c d ⊆
      ⋃ p : boxE a b c d, Metric.ball (p : EuclideanSpace ℝ (Fin 2)) (r p) := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    simpa [Metric.mem_ball] using hr ⟨x, hx⟩
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) hK.isClosed
    (fun p : boxE a b c d => Metric.ball (p : EuclideanSpace ℝ (Fin 2)) (r p))
    (fun _ => Metric.isOpen_ball) hcov
  refine ⟨fun x => ∑ᶠ p : boxE a b c d, f p x • g p x, ?_, ?_⟩
  · exact (f.contMDiff_finsum_smul (g := g)
      (fun p x _ => (hg p).1.contMDiff.contMDiffAt)).contDiff
  · intro x hx0 hx1
    have hxK : x ∈ boxE a b c d := ⟨hx0, hx1⟩
    calc ∑ᶠ p : boxE a b c d, f p x • g p x
        = ∑ p ∈ f.finsupport x, f p x • g p x :=
          (f.sum_finsupport_smul_eq_finsum x g).symm
      _ = ∑ p ∈ f.finsupport x, f p x • u x := by
          refine Finset.sum_congr rfl fun p hp => ?_
          have hfp : f p x ≠ 0 := by
            have hmem := (f.mem_finsupport (x₀ := x)).mp hp
            simpa [Function.mem_support] using hmem
          have hxt : x ∈ tsupport (f p) := subset_tsupport _ (Function.mem_support.mpr hfp)
          have hxU := hf p hxt
          rw [Metric.mem_ball] at hxU
          rw [(hg p).2 x hx0 hx1 hxU]
      _ = (∑ p ∈ f.finsupport x, f p x) • u x :=
          (Finset.sum_smul (s := f.finsupport x) (f := fun p => f p x) (x := u x)).symm
      _ = (1 : ℝ) • u x := by rw [f.sum_finsupport x hxK]
      _ = u x := one_smul ℝ (u x)

/-! ## A smooth retraction of the plane into a neighbourhood of the box -/

/-- **A smooth retraction of the plane into a neighbourhood of the box.**  If `O` is an open set
containing the box `[a,b] × [c,d]`, there is a `C^∞` map `φ : ℝ² → ℝ²` which is the identity on the
box and whose whole image lies in `O`. -/
lemma flattening_into_nhd (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    {O : Set (EuclideanSpace ℝ (Fin 2))} (hO : IsOpen O)
    (hKO : ∀ q : EuclideanSpace ℝ (Fin 2), q 0 ∈ Set.Icc a b → q 1 ∈ Set.Icc c d → q ∈ O) :
    ∃ φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧
      (∀ q : EuclideanSpace ℝ (Fin 2), q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d → φ q = q) ∧
      ∀ q : EuclideanSpace ℝ (Fin 2), φ q ∈ O := by
  by_cases hOuniv : O = Set.univ
  · exact ⟨id, contDiff_id, fun q _ => rfl, fun q => by rw [hOuniv]; exact Set.mem_univ q⟩
  have hKc : IsCompact (boxE a b c d) := boxE_isCompact a b c d hab hcd
  have hKne : (boxE a b c d).Nonempty := by
    refine ⟨WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then (a + b) / 2 else (c + d) / 2), ?_, ?_⟩
    · rw [Set.mem_Icc]; constructor <;> simp <;> linarith
    · rw [Set.mem_Icc]; constructor <;> simp <;> linarith
  -- the distance to the complement of `O` has a positive minimum on the box
  have hcont : Continuous (fun q : EuclideanSpace ℝ (Fin 2) => Metric.infDist q Oᶜ) := by
    refine continuous_iff_continuousAt.mpr fun q => ?_
    rw [Metric.continuousAt_iff]
    intro δ hδ
    refine ⟨δ / 2, by linarith, fun y hy => ?_⟩
    have hy' : dist q y < δ / 2 := by simpa [dist_comm] using hy
    rw [Real.dist_eq, abs_sub_lt_iff]
    have h1 : Metric.infDist q Oᶜ ≤ Metric.infDist y Oᶜ + dist q y :=
      Metric.infDist_le_infDist_add_dist
    have h2 : Metric.infDist y Oᶜ ≤ Metric.infDist q Oᶜ + dist q y := by
      simpa [dist_comm] using (Metric.infDist_le_infDist_add_dist (x := y) (y := q) (s := Oᶜ))
    constructor <;> linarith
  obtain ⟨x₀, hx₀K, hmin⟩ := hKc.exists_isMinOn hKne hcont.continuousOn
  have hne : (Oᶜ).Nonempty := Set.nonempty_compl.mpr hOuniv
  have hδpos : 0 < Metric.infDist x₀ Oᶜ := by
    have hx₀O : x₀ ∈ O := hKO x₀ hx₀K.1 hx₀K.2
    obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.mp hO x₀ hx₀O
    have hle : ρ ≤ Metric.infDist x₀ Oᶜ :=
      (Metric.le_infDist hne).mpr fun y hy => by
        by_contra hlt
        push_neg at hlt
        exact hy (hρO (Metric.mem_ball.mpr (by simpa [dist_comm] using hlt)))
    linarith
  set ε : ℝ := Metric.infDist x₀ Oᶜ / 4 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  -- the `ε`-thickened box is still inside `O`
  have hboxO : ∀ q : EuclideanSpace ℝ (Fin 2),
      q 0 ∈ Set.Ioo (a - ε) (b + ε) → q 1 ∈ Set.Ioo (c - ε) (d + ε) → q ∈ O := by
    intro q hq0 hq1
    set x : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then max a (min b (q 0))
        else max c (min d (q 1))) with hxdef
    have hxval0 : x 0 = max a (min b (q 0)) := by simp [hxdef]
    have hxval1 : x 1 = max c (min d (q 1)) := by simp [hxdef]
    have hx0I : x 0 ∈ Set.Icc a b := by
      rw [hxval0, Set.mem_Icc]
      exact ⟨le_max_left _ _, max_le hab.le (min_le_left _ _)⟩
    have hx1I : x 1 ∈ Set.Icc c d := by
      rw [hxval1, Set.mem_Icc]
      exact ⟨le_max_left _ _, max_le hcd.le (min_le_left _ _)⟩
    have hxK : x ∈ boxE a b c d := ⟨hx0I, hx1I⟩
    have hc0 : |q 0 - x 0| ≤ ε := by
      rw [hxval0]
      rcases le_total (q 0) a with h | h
      · have hmax : max a (min b (q 0)) = a := by
          refine le_antisymm ?_ (le_max_left a (min b (q 0)))
          exact max_le (le_refl a) (le_trans (min_le_right b (q 0)) h)
        rw [hmax, abs_of_nonpos (by linarith)]
        linarith [hq0.1]
      · rcases le_total (q 0) b with h2 | h2
        · have hmax : max a (min b (q 0)) = q 0 := by
            refine le_antisymm ?_ ?_
            · exact max_le h (min_le_right b (q 0))
            · exact le_trans (le_min h2 (le_refl (q 0))) (le_max_right a (min b (q 0)))
          rw [hmax, sub_self, abs_zero]; linarith
        · have hmax : max a (min b (q 0)) = b := by
            refine le_antisymm ?_ ?_
            · exact max_le (by linarith) (min_le_left b (q 0))
            · exact le_trans (le_min (le_refl b) h2) (le_max_right a (min b (q 0)))
          rw [hmax, abs_of_nonneg (by linarith)]
          linarith [hq0.2]
    have hc1 : |q 1 - x 1| ≤ ε := by
      rw [hxval1]
      rcases le_total (q 1) c with h | h
      · have hmax : max c (min d (q 1)) = c := by
          refine le_antisymm ?_ (le_max_left c (min d (q 1)))
          exact max_le (le_refl c) (le_trans (min_le_right d (q 1)) h)
        rw [hmax, abs_of_nonpos (by linarith)]
        linarith [hq1.1]
      · rcases le_total (q 1) d with h2 | h2
        · have hmax : max c (min d (q 1)) = q 1 := by
            refine le_antisymm ?_ ?_
            · exact max_le h (min_le_right d (q 1))
            · exact le_trans (le_min h2 (le_refl (q 1))) (le_max_right c (min d (q 1)))
          rw [hmax, sub_self, abs_zero]; linarith
        · have hmax : max c (min d (q 1)) = d := by
            refine le_antisymm ?_ ?_
            · exact max_le (by linarith) (min_le_left d (q 1))
            · exact le_trans (le_min (le_refl d) h2) (le_max_right c (min d (q 1)))
          rw [hmax, abs_of_nonneg (by linarith)]
          linarith [hq1.2]
    have hdist : dist q x ≤ 2 * ε := by
      calc dist q x = ‖q - x‖ := dist_eq_norm q x
        _ ≤ |(q - x) 0| + |(q - x) 1| := by
              rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_le_iff]
              refine ⟨by positivity, ?_⟩
              rw [Real.norm_eq_abs, Real.norm_eq_abs]
              nlinarith [sq_abs ((q - x) 0), sq_abs ((q - x) 1), abs_nonneg ((q - x) 0),
                abs_nonneg ((q - x) 1), sq_nonneg (|(q - x) 0| + |(q - x) 1|)]
        _ = |q 0 - x 0| + |q 1 - x 1| := by simp
        _ ≤ 2 * ε := by linarith
    have hminx : Metric.infDist x₀ Oᶜ ≤ Metric.infDist x Oᶜ := hmin hxK
    have htri : Metric.infDist x Oᶜ ≤ Metric.infDist q Oᶜ + dist x q :=
      Metric.infDist_le_infDist_add_dist
    have hpos : 0 < Metric.infDist q Oᶜ := by
      have h4 : Metric.infDist x₀ Oᶜ = 4 * ε := by rw [hεdef]; ring
      rw [dist_comm] at htri
      linarith
    by_contra hqO
    have hle : Metric.infDist q Oᶜ ≤ 0 := by
      have := Metric.infDist_le_dist_of_mem (x := q) (s := Oᶜ) (y := q) (show q ∈ Oᶜ from hqO)
      simpa using this
    linarith
  -- the two one-dimensional flattenings
  obtain ⟨f, hfsm, hfid, hfim⟩ := exists_contDiff_flattening a b hab ε hε
  obtain ⟨g, hgsm, hgid, hgim⟩ := exists_contDiff_flattening c d hcd ε hε
  let φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun q =>
    f (q 0) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
      + g (q 1) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  have hφsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := by
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : EuclideanSpace ℝ (Fin 2) =>
      f (q 0) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
        + g (q 1) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
    fun_prop
  have hφid : ∀ q : EuclideanSpace ℝ (Fin 2), q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d →
      φ q = q := by
    intro q hq
    show f (q 0) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
      + g (q 1) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) = q
    ext i
    fin_cases i
    · simp [hfid (q 0) hq.1]
    · simp [hgid (q 1) hq.2]
  have hφO : ∀ q : EuclideanSpace ℝ (Fin 2), φ q ∈ O := by
    intro q
    refine hboxO (φ q) ?_ ?_
    · dsimp only [φ]
      simpa using hfim (q 0)
    · dsimp only [φ]
      simpa using hgim (q 1)
  exact ⟨φ, hφsm, hφid, hφO⟩

/-! ## The target theorem -/

set_option maxHeartbeats 1000000

theorem box_lift_assembly (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    {h : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (EuclideanSpace ℝ (Fin 4))}
    (hh : letI := Work.Drive.projCharted 3
      ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) h
        {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d})
    (hcov : IsCoveringMap (Work.Drive.projOfUnitSphere (n := 3))) :
    ∃ (V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4)) (hV : ∀ x, V x ≠ 0),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧
      ∀ x : EuclideanSpace ℝ (Fin 2), x 0 ∈ Set.Icc a b → x 1 ∈ Set.Icc c d →
        Projectivization.mk ℝ (V x) (hV x) = h x := by
  classical
  -- a continuous unit lift of `h` on the box
  obtain ⟨v, hvcont, hvproj⟩ := exists_lift_box_projOfUnitSphere a b c d hab hcd hh hcov
  -- its total extension (with junk value off the box)
  let vv : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4) :=
    fun q => if hq : q ∈ boxE a b c d then (v q : EuclideanSpace ℝ (Fin 4)) else 0
  have hvv : ∀ q (hq : q ∈ boxE a b c d), vv q = (v q : EuclideanSpace ℝ (Fin 4)) := by
    intro q hq
    simp only [vv]
    exact dif_pos hq
  have hvvcont : ContinuousOn vv (boxE a b c d) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hvcont' : Continuous ((boxE a b c d).domRestrict v) :=
      (continuousOn_iff_continuous_domRestrict).mp hvcont
    have hfun : ((boxE a b c d).domRestrict vv) = fun q : boxE a b c d =>
        (((boxE a b c d).domRestrict v) q : EuclideanSpace ℝ (Fin 4)) := by
      funext q
      exact hvv q.1 q.2
    rw [hfun]
    exact continuous_subtype_val.comp hvcont'
  -- the local pieces
  have hpiece : ∀ p : EuclideanSpace ℝ (Fin 2), p 0 ∈ Set.Icc a b → p 1 ∈ Set.Icc c d →
      ∃ r : ℝ, 0 < r ∧ ∃ g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4),
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
        ∀ x : EuclideanSpace ℝ (Fin 2), x 0 ∈ Set.Icc a b → x 1 ∈ Set.Icc c d →
          dist x p < r → g x = vv x := by
    intro p hp0 hp1
    obtain ⟨r, hr, u, hune, husm, hunorm, hueq⟩ :=
      exists_local_unit_lift_projCharted a b c d hab hcd hh p hp0 hp1
    set S : Set (EuclideanSpace ℝ (Fin 2)) := boxE a b c d ∩ Metric.ball p r with hSdef
    have hSpre : IsPreconnected S :=
      ((convex_boxE a b c d).inter (convex_ball p r)).isPreconnected
    let u' : EuclideanSpace ℝ (Fin 2) → unitSphere 3 := fun q =>
      ⟨u q, by rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hunorm q⟩
    have hu'cont : ContinuousOn u' S := by
      rw [continuousOn_iff_continuous_domRestrict]
      refine Continuous.subtype_mk ?_ _
      exact husm.continuous.comp continuous_subtype_val
    have hvS : ContinuousOn v S := hvcont.mono Set.inter_subset_left
    have hvu : ∀ q ∈ S, projOfUnitSphere (v q) = projOfUnitSphere (u' q) := by
      intro q hq
      have hq' : dist q p < r := Metric.mem_ball.mp hq.2
      have h1 : projOfUnitSphere (u' q) = Projectivization.mk ℝ (u q) (hune q) := by
        rw [projOfUnitSphere_eq, projOfUnit_eq_mk]
      exact (hvproj q hq.1.1 hq.1.2).trans
        ((h1.trans (hueq q hq.1.1 hq.1.2 hq')).symm)
    rcases lift_eq_or_neg_of_isPreconnected hcov hSpre hvS hu'cont hvu
      (p := p) ⟨⟨hp0, hp1⟩, by rw [Metric.mem_ball]; simpa using hr⟩ with hcase | hcase
    · refine ⟨r, hr, u, husm, fun x hx0 hx1 hd => ?_⟩
      have hxS : x ∈ S := ⟨⟨hx0, hx1⟩, by rw [Metric.mem_ball]; exact hd⟩
      have h1 : (v x : EuclideanSpace ℝ (Fin 4)) = u x := congrArg Subtype.val (hcase x hxS)
      rw [hvv x ⟨hx0, hx1⟩, h1]
    · refine ⟨r, hr, fun y => -u y, husm.neg, fun x hx0 hx1 hd => ?_⟩
      have hxS : x ∈ S := ⟨⟨hx0, hx1⟩, by rw [Metric.mem_ball]; exact hd⟩
      have h1 : (v x : EuclideanSpace ℝ (Fin 4)) = -u x := by
        have h2 := congrArg Subtype.val (hcase x hxS)
        rw [negSphere_coe] at h2
        simpa using h2
      rw [hvv x ⟨hx0, hx1⟩, h1]
  -- glue the pieces into a global smooth map
  obtain ⟨G, hGsm, hGK⟩ := glue_local_pieces_box a b c d hab hcd (u := vv) hpiece
  -- `G` is nowhere zero on the box, hence on a neighbourhood of it
  have hGne : ∀ q, q ∈ boxE a b c d → G q ≠ 0 := by
    intro q hq
    have h1 : G q = (v q : EuclideanSpace ℝ (Fin 4)) := by
      rw [hGK q hq.1 hq.2, hvv q hq]
    rw [h1]
    exact norm_eq_one_ne_zero (norm_coe_unitSphere (v q))
  have hOpen : IsOpen {q : EuclideanSpace ℝ (Fin 2) | G q ≠ 0} := by
    have hcl : IsClosed {q : EuclideanSpace ℝ (Fin 2) | G q = 0} :=
      isClosed_singleton.preimage hGsm.continuous
    have hset : {q : EuclideanSpace ℝ (Fin 2) | G q ≠ 0} = {q : EuclideanSpace ℝ (Fin 2) |
        G q = 0}ᶜ := by
      ext q
      simp
    rw [hset]
    exact hcl.isOpen_compl
  obtain ⟨φ, hφsm, hφid, hφO⟩ := flattening_into_nhd a b c d hab hcd hOpen
    (fun q hq0 hq1 => hGne q ⟨hq0, hq1⟩)
  refine ⟨fun x => G (φ x), fun x => hφO x, hGsm.comp hφsm, ?_⟩
  intro x hx0 hx1
  have hφx : φ x = x := hφid x ⟨hx0, hx1⟩
  have hvec : G (φ x) = (v x : EuclideanSpace ℝ (Fin 4)) := by
    rw [hφx, hGK x hx0 hx1, hvv x ⟨hx0, hx1⟩]
  have hne_phi : G (φ x) ≠ 0 := hφO x
  have hne_v : (v x : EuclideanSpace ℝ (Fin 4)) ≠ 0 :=
    norm_eq_one_ne_zero (norm_coe_unitSphere (v x))
  exact (mk_eq_mk_of_eq hvec hne_phi hne_v).trans
    ((mk_coe_eq_projOfUnitSphere (v x) hne_v).trans (hvproj x hx0 hx1))

end

end Work.Drive
