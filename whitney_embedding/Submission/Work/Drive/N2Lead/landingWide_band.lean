import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.swlLanding
import Submission.Work.Drive.N2.saddleWindow_legality
import Submission.Work.Drive.N2.journeyAvoidsWide
import Submission.Work.Drive.N2.levelBoundsOfJourney

/-!
# R1: the two-sided wide landing

`Work.Drive.N2Lead.landingWide_band`: a box point `y` of the wide band `(f p − lam0²η, f p + lam0²η)`
reaches *any* level `b` of that band under the datum flow, `f (D.Φ (b − f y, y)) = b`.

`Work.Drive.N2.swlLandingOfBox` is the case `b = f p − lam0²η` (a backward journey only); the proof
below is the version with an arbitrary target, i.e. with the journey running in either direction.

The two ingredients are

* **the trap** (`lw_trap`): along the orbit the level at time `u` lies between `f x` and `f x + u`
  (the forward half is `WindowDatum.hmono` + the global unit-speed bound `orbit_pair_bound`, the
  backward half is the restarted form of the same two);
* **the avoidance of the small model ball of the marked chart** (`lw_core`): a point of the small
  model ball (`modelBall φ' lam0`, `lam0 = ρ j / 8`) which is reached from a box point at a time of
  the wide band is impossible.  The maximal run of the orbit inside the chart region `C j` starting
  from that point is either confined all the way back to the box point — then `WindowDatum.him`
  transports `Im (Zs ·)²` and the entry inequality `lam0² ≤ |Im (Zs y)²|` of the box condition is
  violated (the value of `Im` inside the small ball is `< lam0²` strictly) — or it leaves `C j` at a
  point of chart norm `≥ ρ j = 8 lam0`, where on the one hand `‖Zs‖⁴ = Re (Zs²)² + Im (Zs²)²` is at
  least `4096 lam0⁴` while on the other hand the value window gives `|Re (Zs²)| ≤ lam0²η < lam0²`,
  whence `‖Zs‖⁴ < lam0⁴ + lam0⁴ = 2 lam0⁴ < 4096 lam0⁴`.
* the model balls of the other charts are excluded by value separation
  (`Work.Drive.N2.sepClosedModelBall`) against the value window.

The hypothesis `η < 1/10` of the statement is all the arithmetic that is used (`η² < 1`, `η < 1`).
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set

set_option maxHeartbeats 1000000

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ## The trap -/

/-- **The two-sided trap**: along the datum flow the level of the orbit of `x` at time `u` is caught
between `f x` and `f x + u`. -/
lemma lw_trap {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) (x : M) (u : ℝ) :
    min (f x) (f x + u) ≤ f (D.Φ (u, x)) ∧ f (D.Φ (u, x)) ≤ max (f x) (f x + u) := by
  rcases le_or_gt 0 u with hu | hu
  · refine ⟨?_, ?_⟩
    · rw [min_eq_left (by linarith : f x ≤ f x + u)]
      have h : f (D.Φ ((0 : ℝ), x)) ≤ f (D.Φ (u, x)) :=
        D.hmono x (le_refl (0 : ℝ)) hu hu
      rwa [D.hΦ0 x] at h
    · rw [max_eq_right (by linarith : f x ≤ f x + u)]
      have h := Work.Drive.N2.orbit_pair_bound D x 0 u hu
      rw [D.hΦ0 x] at h
      linarith
  · refine ⟨?_, ?_⟩
    · rw [min_eq_right (by linarith : f x + u ≤ f x)]
      have h := Work.Drive.N2.orbit_pair_bound D x u 0 hu.le
      rw [D.hΦ0 x] at h
      linarith
    · rw [max_eq_left (by linarith : f x + u ≤ f x)]
      have h : f (D.Φ ((0 : ℝ), D.Φ (u, x))) ≤ f (D.Φ (-u, D.Φ (u, x))) :=
        D.hmono (D.Φ (u, x)) (le_refl (0 : ℝ))
          (show (0 : ℝ) ≤ -u from by linarith) (by linarith)
      rw [D.hΦ0, D.hΦcomp (-u) u x, neg_add_cancel, D.hΦ0 x] at h
      exact h

/-- **The value window along the journey**: if the starting level `f x` and the target level `b` both
lie strictly inside the wide band, then the whole journey from `x` to the level `b` stays strictly
inside the band. -/
lemma lw_band {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {x : M} {lam0 η b : ℝ}
    (hlo : f p - lam0 ^ 2 * η < f x) (hhi : f x < f p + lam0 ^ 2 * η)
    (hb_lo : f p - lam0 ^ 2 * η < b) (hb_hi : b < f p + lam0 ^ 2 * η) :
    ∀ u ∈ Set.Icc (min 0 (b - f x)) (max 0 (b - f x)),
      f p - lam0 ^ 2 * η < f (D.Φ (u, x)) ∧ f (D.Φ (u, x)) < f p + lam0 ^ 2 * η := by
  set τ : ℝ := b - f x with hτdef
  have hbτ : f x + τ = b := by rw [hτdef]; ring
  intro u hu
  obtain ⟨hmin_u, hmax_u⟩ := lw_trap D x u
  rw [Set.mem_Icc] at hu
  obtain ⟨hu1, hu2⟩ := hu
  rcases le_or_gt 0 τ with hτ | hτ
  · rw [min_eq_left hτ] at hu1
    rw [max_eq_right hτ] at hu2
    have h1 : f x ≤ f (D.Φ (u, x)) := by
      have hmin : min (f x) (f x + u) = f x := min_eq_left (by linarith)
      rwa [hmin] at hmin_u
    have h2 : f (D.Φ (u, x)) ≤ f x + u := by
      have hmax : max (f x) (f x + u) = f x + u := max_eq_right (by linarith)
      rwa [hmax] at hmax_u
    exact ⟨by linarith, by linarith [hbτ, hu2, hb_hi]⟩
  · rw [min_eq_right hτ.le] at hu1
    rw [max_eq_left hτ.le] at hu2
    have h1 : f x + u ≤ f (D.Φ (u, x)) := by
      have hmin : min (f x) (f x + u) = f x + u := min_eq_right (by linarith)
      rwa [hmin] at hmin_u
    have h2 : f (D.Φ (u, x)) ≤ f x := by
      have hmax : max (f x) (f x + u) = f x := max_eq_left (by linarith)
      rwa [hmax] at hmax_u
    exact ⟨by linarith [hbτ, hu1, hb_lo], by linarith [hhi, h2]⟩

/-! ## A box point of the band is off the small model ball -/

/-- **A box point of the wide band is off the small model ball.**  If `x` were in
`modelBall φ' lam0`, its chart norm would be `< lam0 = ρ j / 8`, contradicting the box condition:
either `x` is off the ball of radius `ρ j`, or the invariant `|Im (Zs x)²|` is at least
`c₀ lam0² > lam0²`, while inside the small ball it is `< lam0²`. -/
lemma lw_notMem_smallBall {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (Zs : M → ℂ) (lam0 : ℝ)
    (hlam0 : lam0 = D.ρ D.j / 8)
    (hsrc : φ'.source = (D.φ D.j).source)
    (hball : ∀ r : ℝ, Work.Drive.N2.modelBall φ' r = Work.Drive.N2.modelBall (D.φ D.j) r)
    (hZs : ∀ y : M, Zs y = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + ((Zs y) ^ 2).re)
    {η c₀ : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hc₀ : 1 < c₀)
    {x : M}
    (hbox : x ∉ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) ∨
      c₀ * lam0 ^ 2 ≤ |((Zs x) ^ 2).im|)
    (hband : f x ∈ Set.Ioo (f p - lam0 ^ 2 * η) (f p + lam0 ^ 2 * η)) :
    x ∉ Work.Drive.N2.modelBall φ' lam0 := by
  intro hmem
  have hlam0pos : 0 < lam0 := by rw [hlam0]; exact div_pos (D.hρ D.j) (by norm_num)
  have hρpos : 0 < D.ρ D.j := D.hρ D.j
  rcases hbox with hA | hB
  · have hmem' : x ∈ Work.Drive.N2.modelBall (D.φ D.j) lam0 := by
      rw [← hball lam0]; exact hmem
    have hmem'' : x ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) :=
      ⟨hmem'.1, by rw [hlam0] at hmem'; linarith [hmem'.2, hρpos]⟩
    exact hA hmem''
  · have hnorm : ‖Zs x‖ < lam0 := by
      rw [Work.Drive.N2.swlL_Zs_norm φ' Zs hZs x]
      exact hmem.2
    have h1 : |((Zs x) ^ 2).im| ≤ ‖(Zs x) ^ 2‖ := Complex.abs_im_le_norm _
    have h2 : ‖(Zs x) ^ 2‖ = ‖Zs x‖ ^ 2 := norm_pow _ 2
    have h3 : |((Zs x) ^ 2).im| < lam0 ^ 2 := by
      rw [h2] at h1
      nlinarith [h1, hnorm, norm_nonneg (Zs x)]
    have h4 : lam0 ^ 2 < c₀ * lam0 ^ 2 := by nlinarith [hc₀, pow_pos hlam0pos 2]
    linarith

/-! ## The entry inequality -/

/-- **The entry inequality**: on the chart region, a box point of the wide band satisfies
`lam0² ≤ |Im (Zs ·)²|`. -/
lemma lw_entry_ineq {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (Zs : M → ℂ) (lam0 : ℝ)
    (hlam0 : lam0 = D.ρ D.j / 8)
    (hsrc : φ'.source = (D.φ D.j).source)
    (hball : ∀ r : ℝ, Work.Drive.N2.modelBall φ' r = Work.Drive.N2.modelBall (D.φ D.j) r)
    (hZs : ∀ y : M, Zs y = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + ((Zs y) ^ 2).re)
    {η c₀ : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hc₀ : 1 < c₀)
    {w : M} (hwC : w ∈ D.C D.j)
    (hbox : w ∉ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) ∨
      c₀ * lam0 ^ 2 ≤ |((Zs w) ^ 2).im|)
    (hband : f w ∈ Set.Ioo (f p - lam0 ^ 2 * η) (f p + lam0 ^ 2 * η)) :
    lam0 ^ 2 ≤ |((Zs w) ^ 2).im| := by
  have hlam0pos : 0 < lam0 := by rw [hlam0]; exact div_pos (D.hρ D.j) (by norm_num)
  have hwsrcJ : w ∈ (D.φ D.j).source := D.hCsub D.j hwC
  rcases hbox with hA | hB
  · have hnormw : ‖D.φ D.j w‖ = ‖φ' w‖ :=
      Work.Drive.N2.swlL_norm_eq_of_modelBall_eq (D.φ D.j) φ' hsrc hball hwsrcJ
    have hR : D.ρ D.j ≤ ‖φ' w‖ := by
      have h1 : D.ρ D.j ≤ ‖D.φ D.j w‖ := by
        by_contra hc
        rw [not_le] at hc
        exact hA ⟨hwsrcJ, hc⟩
      rwa [hnormw] at h1
    have h8 : (8 : ℝ) * lam0 ≤ ‖φ' w‖ := by
      have hρ8 : D.ρ D.j = 8 * lam0 := by rw [hlam0]; ring
      rw [← hρ8]; exact hR
    have h4 : ((8 : ℝ) * lam0) ^ 4 ≤ ‖φ' w‖ ^ 4 := pow_le_pow_left₀ (by positivity) h8 4
    have hdecomp : ‖φ' w‖ ^ 4 = ((Zs w) ^ 2).re ^ 2 + ((Zs w) ^ 2).im ^ 2 :=
      Work.Drive.N2.swlL_Zs_fourth φ' Zs hZs w
    rw [hdecomp] at h4
    have h8v : ((8 : ℝ) * lam0) ^ 4 = 4096 * lam0 ^ 4 := by ring
    rw [h8v] at h4
    have hrew : ((Zs w) ^ 2).re = f w - f p := by
      have h0 := hlev w hwsrcJ
      linarith
    rw [hrew] at h4
    have habs : |f w - f p| < lam0 ^ 2 * η :=
      abs_lt.mpr ⟨by linarith [hband.1], by linarith [hband.2]⟩
    have hre2 : (f w - f p) ^ 2 < lam0 ^ 4 := by
      have hsq : (f w - f p) ^ 2 < (lam0 ^ 2 * η) ^ 2 := by
        rw [sq_lt_sq, abs_of_pos (by positivity : (0 : ℝ) < lam0 ^ 2 * η)]
        exact habs
      have hη2 : η ^ 2 < 1 := by nlinarith [hη, hη']
      have hstep : (lam0 ^ 2 * η) ^ 2 < lam0 ^ 4 := by
        have h1 : (lam0 ^ 2 * η) ^ 2 = lam0 ^ 4 * η ^ 2 := by ring
        have h2 : lam0 ^ 4 * η ^ 2 < lam0 ^ 4 * 1 :=
          mul_lt_mul_of_pos_left hη2 (by positivity : (0 : ℝ) < lam0 ^ 4)
        linarith
      linarith
    have him2 : (lam0 ^ 2) ^ 2 < ((Zs w) ^ 2).im ^ 2 := by
      have h8v : ((8 : ℝ) * lam0) ^ 4 = 4096 * lam0 ^ 4 := by ring
      nlinarith [h4, h8v, hre2]
    have h := (sq_lt_sq (a := lam0 ^ 2) (b := ((Zs w) ^ 2).im)).mp him2
    rw [abs_of_nonneg (sq_nonneg lam0)] at h
    exact le_of_lt h
  · have h0pos : (0 : ℝ) < lam0 ^ 2 := pow_pos hlam0pos 2
    calc lam0 ^ 2 = 1 * lam0 ^ 2 := by ring
      _ ≤ c₀ * lam0 ^ 2 := by nlinarith [hc₀, h0pos]
      _ ≤ |((Zs w) ^ 2).im| := hB

/-! ## The core contradiction -/

/-- **The core contradiction**: a bad point cannot be reached from a box point along a journey whose
values lie in the wide band and along which `Im (Zs ·)²` is constant on every chart-confined piece.

Here `γ` is the journey (`γ 0 = z` the bad point, `γ L = w` the box point), `L > 0` its length,
`himγ` the transport of `Im (Zs ·)²` along confined pieces and `hwin` the value window. -/
theorem lw_core {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (Zs : M → ℂ) (lam0 : ℝ)
    (hlam0 : lam0 = D.ρ D.j / 8)
    (hsrc : φ'.source = (D.φ D.j).source)
    (hball : ∀ r : ℝ, Work.Drive.N2.modelBall φ' r = Work.Drive.N2.modelBall (D.φ D.j) r)
    (hZs : ∀ y : M, Zs y = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + ((Zs y) ^ 2).re)
    {η c₀ : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hc₀ : 1 < c₀)
    {L : ℝ} (hL : 0 < L) {z w : M}
    (hzC : z ∈ D.C D.j) (hznorm : ‖φ' z‖ < lam0)
    (hboxw : w ∉ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) ∨
      c₀ * lam0 ^ 2 ≤ |((Zs w) ^ 2).im|)
    (hbandw : f w ∈ Set.Ioo (f p - lam0 ^ 2 * η) (f p + lam0 ^ 2 * η))
    (γ : ℝ → M) (hγ0 : γ 0 = z) (hγL : γ L = w) (hγcont : Continuous γ)
    (hwin : ∀ s ∈ Set.Icc 0 L, |f (γ s) - f p| ≤ lam0 ^ 2 * η)
    (himγ : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ L →
      (∀ s ∈ Set.Icc a b, γ s ∈ D.C D.j) →
      ((Zs (γ b)) ^ 2).im = ((Zs (γ a)) ^ 2).im)
    (hlevγ : ∀ s ∈ Set.Icc 0 L, γ s ∈ (D.φ D.j).source →
      f (γ s) = f p + ((Zs (γ s)) ^ 2).re) : False := by
  have hlam0pos : 0 < lam0 := by rw [hlam0]; exact div_pos (D.hρ D.j) (by norm_num)
  -- the maximal confined run of the journey starting at the bad point
  set E : Set ℝ := {s : ℝ | s ∈ Set.Icc 0 L ∧ ∀ v ∈ Set.Icc 0 s, γ v ∈ D.C D.j} with hE
  have hE0 : (0 : ℝ) ∈ E := by
    refine ⟨⟨le_rfl, hL.le⟩, fun v hv => ?_⟩
    rw [Set.mem_Icc] at hv
    have hv0 : v = 0 := le_antisymm hv.2 hv.1
    rw [hv0, hγ0]
    exact hzC
  have hEne : E.Nonempty := ⟨0, hE0⟩
  have hEbdd : BddAbove E := ⟨L, fun s hs => by rw [hE] at hs; exact hs.1.2⟩
  set a : ℝ := sSup E with ha
  have ha0 : 0 ≤ a := by rw [ha]; exact le_csSup hEbdd hE0
  have haL : a ≤ L := by
    rw [ha]
    exact csSup_le hEne (fun s hs => by rw [hE] at hs; exact hs.1.2)
  have hacl : a ∈ closure E := by rw [ha]; exact csSup_mem_closure hEne hEbdd
  have hconf : ∀ s ∈ Set.Icc 0 a, γ s ∈ D.C D.j := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · obtain ⟨u, huE, hsu⟩ :=
        (lt_csSup_iff hEbdd hEne).mp (show s < sSup E by rw [← ha]; exact hlt)
      rw [hE] at huE
      exact huE.2 s ⟨hs.1, le_of_lt hsu⟩
    · subst heq
      have himg : γ a ∈ γ '' closure E := ⟨a, hacl, rfl⟩
      have hsub : γ '' E ⊆ D.C D.j := by
        rintro _ ⟨u, huE, rfl⟩
        rw [hE] at huE
        exact huE.2 u ⟨huE.1.1, le_rfl⟩
      have hcl : closure (γ '' E) ⊆ D.C D.j := by
        rw [← (D.hCclosed D.j).closure_eq]
        exact closure_mono hsub
      exact hcl ((image_closure_subset_closure_image hγcont) himg)
  -- the invariant at the bad point and at the exit
  have hbz : |((Zs z) ^ 2).im| < lam0 ^ 2 := by
    have hnorm : ‖Zs z‖ < lam0 := by
      rw [Work.Drive.N2.swlL_Zs_norm φ' Zs hZs z]; exact hznorm
    have h1 : |((Zs z) ^ 2).im| ≤ ‖(Zs z) ^ 2‖ := Complex.abs_im_le_norm _
    have h2 : ‖(Zs z) ^ 2‖ = ‖Zs z‖ ^ 2 := norm_pow _ 2
    rw [h2] at h1
    nlinarith [h1, hnorm, norm_nonneg (Zs z)]
  have hima : ((Zs (γ a)) ^ 2).im = ((Zs z) ^ 2).im := by
    have h := himγ (a := 0) (b := a) (le_refl (0 : ℝ)) ha0 haL hconf
    rw [hγ0] at h
    exact h
  rcases lt_or_eq_of_le haL with halt | haeq
  · -- the run leaves the chart region at `a`
    have haC : γ a ∈ D.C D.j := hconf a ⟨ha0, le_rfl⟩
    have hρle : D.ρ D.j ≤ ‖φ' (γ a)‖ := by
      by_contra hcon
      push_neg at hcon
      have hζsrc : γ a ∈ φ'.source := by rw [hsrc]; exact D.hCsub D.j haC
      have hint : γ a ∈ interior (D.C D.j) :=
        Work.Drive.N2.swlL_mem_interior_C D φ' hball hζsrc hcon
      have hnhds : γ ⁻¹' interior (D.C D.j) ∈ 𝓝 a :=
        hγcont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hint)
      obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hnhds
      set s : ℝ := a + min ε (L - a) / 2 with hsdef
      have hminpos : 0 < min ε (L - a) := lt_min hεpos (by linarith)
      have hsa : a < s := by rw [hsdef]; linarith
      have hsL : s ≤ L := by
        rw [hsdef]
        have h2 : min ε (L - a) ≤ L - a := min_le_right _ _
        linarith
      have hsE : s ∈ E := by
        refine ⟨⟨le_trans ha0 hsa.le, hsL⟩, fun v hv => ?_⟩
        rcases le_or_gt v a with hva | hva
        · exact hconf v ⟨hv.1, hva⟩
        · have hd : dist v a < ε := by
            rw [Real.dist_eq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ v - a)]
            have h3 : min ε (L - a) ≤ ε := min_le_left _ _
            rw [hsdef] at hv
            linarith [hv.2, h3]
          exact interior_subset (hε (Metric.mem_ball.mpr hd))
      exact absurd (le_csSup hEbdd hsE) (not_le.mpr hsa)
    have hIma : |((Zs (γ a)) ^ 2).im| < lam0 ^ 2 := by rw [hima]; exact hbz
    have hnorm4 : ‖φ' (γ a)‖ ^ 4 = ((Zs (γ a)) ^ 2).re ^ 2 + ((Zs (γ a)) ^ 2).im ^ 2 :=
      Work.Drive.N2.swlL_Zs_fourth φ' Zs hZs (γ a)
    have h8 : ((8 : ℝ) * lam0) ^ 4 ≤ ‖φ' (γ a)‖ ^ 4 := by
      have hρ8 : D.ρ D.j = 8 * lam0 := by rw [hlam0]; ring
      calc ((8 : ℝ) * lam0) ^ 4 = (D.ρ D.j) ^ 4 := by rw [hρ8]
        _ ≤ ‖φ' (γ a)‖ ^ 4 := pow_le_pow_left₀ (D.hρ D.j).le hρle 4
    have hIm2 : ((Zs (γ a)) ^ 2).im ^ 2 < lam0 ^ 4 := by
      have h1 : |((Zs (γ a)) ^ 2).im| ^ 2 < (lam0 ^ 2) ^ 2 :=
        pow_lt_pow_left₀ hIma (abs_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)
      rwa [sq_abs, show (lam0 ^ 2) ^ 2 = lam0 ^ 4 by ring] at h1
    have hre2 : (lam0 ^ 2) ^ 2 < ((Zs (γ a)) ^ 2).re ^ 2 := by
      have h8v : ((8 : ℝ) * lam0) ^ 4 = 4096 * lam0 ^ 4 := by ring
      nlinarith [hnorm4, h8, h8v, hIm2, pow_pos hlam0pos 4]
    have hre_lt : lam0 ^ 2 < |((Zs (γ a)) ^ 2).re| := by
      have h := (sq_lt_sq (a := lam0 ^ 2) (b := ((Zs (γ a)) ^ 2).re)).mp hre2
      rwa [abs_of_nonneg (sq_nonneg lam0)] at h
    have hwin_a : |f (γ a) - f p| ≤ lam0 ^ 2 * η := hwin a ⟨ha0, haL⟩
    have hreeq : ((Zs (γ a)) ^ 2).re = f (γ a) - f p := by
      have h := hlevγ a ⟨ha0, haL⟩ (D.hCsub D.j haC)
      linarith
    have hηlt : lam0 ^ 2 * η < lam0 ^ 2 := by nlinarith [hη, hη', pow_pos hlam0pos 2]
    rw [hreeq] at hre_lt
    linarith [hre_lt, hwin_a, hηlt]
  · -- the run reaches the box point
    have hγa : γ a = w := by rw [haeq, hγL]
    have hwC : w ∈ D.C D.j := by rw [← hγa]; exact hconf a ⟨ha0, le_rfl⟩
    have hH := lw_entry_ineq D φ' Zs lam0 hlam0 hsrc hball hZs hlev hη hη' hc₀ hwC hboxw hbandw
    have hbw : |((Zs w) ^ 2).im| < lam0 ^ 2 := by
      have h1 : ((Zs w) ^ 2).im = ((Zs z) ^ 2).im := by
        have h := hima
        rw [hγa] at h
        exact h
      rw [h1]; exact hbz
    linarith

/-! ## The two-sided wide landing -/

open scoped Manifold ContDiff in
/-- **R1: the two-sided wide landing** (`NOTES_LEAD_saddlePacket.md` §2): a box point of the wide band `(f p − lam0²η, f p + lam0²η)` reaches *any* level `b` of that band under the datum flow, `f (D.Φ (b − f y, y)) = b`.  `Work.Drive.N2.swlLandingOfBox` is the case `b = f p − lam0²η` (a backward journey only); this is the version with an arbitrary target (used with the *forward* target `u⁺ = f p + 3η/2` by `saddlePin_oneComp_or`). -/
theorem landingWide_band {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hsgn : D.s₁ D.j = - D.s₂ D.j)
    (φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (Zs : M → ℂ) (lam0 : ℝ)
    (hlam0 : lam0 = D.ρ D.j / 8)
    (hsrc : φ'.source = (D.φ D.j).source)
    (hball : ∀ r : ℝ, Work.Drive.N2.modelBall φ' r = Work.Drive.N2.modelBall (D.φ D.j) r)
    (hZs : ∀ y : M, Zs y = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + ((Zs y) ^ 2).re)
    (him : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      ((Zs (D.Φ (t, y))) ^ 2).im = ((Zs y) ^ 2).im)
    {η c₀ : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hc₀ : 1 < c₀)
    (hsep : (D.ρ D.j / 8) ^ 2 * η < 2 * D.ηd)
    {y : M}
    (hbox : y ∉ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) ∨
      c₀ * lam0 ^ 2 ≤ |((Zs y) ^ 2).im|)
    (hyband : f y ∈ Set.Ioo (f p - lam0 ^ 2 * η) (f p + lam0 ^ 2 * η))
    {b : ℝ} (hb : b ∈ Set.Ioo (f p - lam0 ^ 2 * η) (f p + lam0 ^ 2 * η)) :
    f (D.Φ (b - f y, y)) = b := by
  classical
  set τ : ℝ := b - f y with hτdef
  have hlam0pos : 0 < lam0 := by rw [hlam0]; exact div_pos (D.hρ D.j) (by norm_num)
  have hband_lo : f p - lam0 ^ 2 * η < f y := hyband.1
  have hband_hi : f y < f p + lam0 ^ 2 * η := hyband.2
  have hb_lo : f p - lam0 ^ 2 * η < b := hb.1
  have hb_hi : b < f p + lam0 ^ 2 * η := hb.2
  -- a box point is off the small ball
  have hy_not_small : y ∉ Work.Drive.N2.modelBall φ' lam0 :=
    lw_notMem_smallBall D φ' Zs lam0 hlam0 hsrc hball hZs hlev hη hη' hc₀ hbox hyband
  -- the value window along the journey
  have hwin : ∀ u ∈ Set.Icc (min 0 τ) (max 0 τ), |f (D.Φ (u, y)) - f p| ≤ lam0 ^ 2 * η := by
    intro u hu
    have h := lw_band D (x := y) hband_lo hband_hi hb_lo hb_hi u hu
    exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  -- the marked small model ball is avoided
  have hB8 : ∀ u ∈ Set.Icc (min 0 τ) (max 0 τ),
      D.Φ (u, y) ∉ Work.Drive.N2.modelBall φ' lam0 := by
    intro u₀ hu₀ hmem
    have hune : u₀ ≠ 0 := by
      rintro rfl
      exact hy_not_small (by rwa [D.hΦ0 y] at hmem)
    have hzC : D.Φ (u₀, y) ∈ D.C D.j := by
      have h1 : D.Φ (u₀, y) ∈ Work.Drive.N2.modelBall (D.φ D.j) lam0 := by
        rw [← hball lam0]; exact hmem
      rw [show lam0 = D.ρ D.j / 8 from hlam0] at h1
      exact D.hCball D.j h1
    have hznorm : ‖φ' (D.Φ (u₀, y))‖ < lam0 := hmem.2
    rcases le_or_gt u₀ 0 with hle | hgt
    · -- the journey to the target runs forward in the datum parameter
      have hL : 0 < -u₀ := by
        have : u₀ < 0 := lt_of_le_of_ne hle hune
        linarith
      refine lw_core D φ' Zs lam0 hlam0 hsrc hball hZs hlev hη hη' hc₀ hL hzC hznorm
        hbox hyband (fun s => D.Φ (s, D.Φ (u₀, y))) ?_ ?_ ?_ ?_ ?_ ?_
      · exact D.hΦ0 _
      · rw [D.hΦcomp (-u₀) u₀ y, neg_add_cancel, D.hΦ0 y]
      · exact D.hΦsm.continuous.comp (continuous_id.prodMk continuous_const)
      · intro s hs
        rw [D.hΦcomp s u₀ y]
        have hmemI : s + u₀ ∈ Set.Icc (min 0 τ) (max 0 τ) :=
          ⟨by linarith [hs.1, hu₀.1], by linarith [hs.2, le_max_left (0 : ℝ) τ]⟩
        exact hwin (s + u₀) hmemI
      · intro a b ha hab hbL hconf'
        have hconf'' : ∀ v ∈ Set.Icc (u₀ + a) (u₀ + b), D.Φ (v, y) ∈ D.C D.j := by
          intro v hv
          have hv' : v - u₀ ∈ Set.Icc a b := ⟨by linarith [hv.1], by linarith [hv.2]⟩
          have h2 := hconf' (v - u₀) hv'
          rwa [D.hΦcomp (v - u₀) u₀ y, sub_add_cancel] at h2
        have h := Work.Drive.N2.swlL_im_eq D Zs him (by linarith : u₀ + a ≤ u₀ + b) hconf''
        rw [D.hΦcomp b u₀ y, D.hΦcomp a u₀ y,
          show b + u₀ = u₀ + b by ring, show a + u₀ = u₀ + a by ring]
        exact h
      · intro s hs hsrc'
        rw [D.hΦcomp s u₀ y] at hsrc' ⊢
        exact hlev _ hsrc'
    · -- the journey to the target runs backward in the datum parameter
      have hL : 0 < u₀ := hgt
      have h0τ : 0 ≤ τ := by
        by_contra hc
        rw [not_le] at hc
        have hmax0 : max 0 τ = 0 := max_eq_left hc.le
        linarith [hu₀.2, hmax0, hgt]
      have hu₀' : 0 ≤ u₀ ∧ u₀ ≤ τ := by
        rw [Set.mem_Icc, min_eq_left h0τ, max_eq_right h0τ] at hu₀
        exact hu₀
      refine lw_core D φ' Zs lam0 hlam0 hsrc hball hZs hlev hη hη' hc₀ hL hzC hznorm
        hbox hyband (fun s => D.Φ (-s, D.Φ (u₀, y))) ?_ ?_ ?_ ?_ ?_ ?_
      · rw [neg_zero, D.hΦ0]
      · rw [D.hΦcomp (-u₀) u₀ y, neg_add_cancel, D.hΦ0 y]
      · exact D.hΦsm.continuous.comp (continuous_id.neg.prodMk continuous_const)
      · intro s hs
        rw [D.hΦcomp (-s) u₀ y]
        have hmemI : -s + u₀ ∈ Set.Icc (min 0 τ) (max 0 τ) := by
          rw [min_eq_left h0τ, max_eq_right h0τ]
          exact ⟨by linarith [hs.2], by linarith [hs.1, hu₀'.2]⟩
        exact hwin (-s + u₀) hmemI
      · intro a b ha hab hbL hconf'
        have hconf'' : ∀ v ∈ Set.Icc (u₀ - b) (u₀ - a), D.Φ (v, y) ∈ D.C D.j := by
          intro v hv
          have hv' : u₀ - v ∈ Set.Icc a b := ⟨by linarith [hv.2], by linarith [hv.1]⟩
          have h2 := hconf' (u₀ - v) hv'
          rwa [show -(u₀ - v) = v - u₀ by ring, D.hΦcomp (v - u₀) u₀ y, sub_add_cancel] at h2
        have h := Work.Drive.N2.swlL_im_eq D Zs him (by linarith : u₀ - b ≤ u₀ - a) hconf''
        rw [D.hΦcomp (-b) u₀ y, D.hΦcomp (-a) u₀ y,
          show -b + u₀ = u₀ - b by ring, show -a + u₀ = u₀ - a by ring]
        exact h.symm
      · intro s hs hsrc'
        rw [D.hΦcomp (-s) u₀ y] at hsrc' ⊢
        exact hlev _ hsrc'
  -- the model balls of the other charts are avoided by value separation
  have hOther : ∀ u ∈ Set.Icc (min 0 τ) (max 0 τ), ∀ i : Fin D.N, i ≠ D.j →
      D.Φ (u, y) ∉ Work.Drive.N2.modelBall (D.φ i) (D.ρ i / 8) := by
    intro u hu i hi hmem
    have h1 := Work.Drive.N2.sepClosedModelBall D hi (D.Φ (u, y)) (subset_closure hmem)
    have h2 := hwin u hu
    have hsepη : lam0 ^ 2 * η < 2 * D.ηd := by rw [hlam0]; exact hsep
    linarith
  have havoid : ∀ u ∈ Set.Icc (min 0 τ) (max 0 τ), ∀ i : Fin D.N,
      D.Φ (u, y) ∉ Work.Drive.N2.modelBall (D.φ i) (D.ρ i / 8) := by
    intro u hu i
    by_cases hi : i = D.j
    · subst hi
      have h' := hB8 u hu
      rw [show D.ρ D.j / 8 = lam0 from by rw [hlam0], ← hball lam0]
      exact h'
    · exact hOther u hu i hi
  have hland := D.hlevel y τ havoid
  rw [hland, hτdef]
  ring

end Work.Drive.N2Lead
