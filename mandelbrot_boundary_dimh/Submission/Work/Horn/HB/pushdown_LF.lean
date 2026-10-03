import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.basic
import Submission.Work.Horn.pushdown_covering
import Submission.Work.Horn.homeomorph_image_of_injOn
import Submission.Work.BasinSC.Tower.connectedComponentIn_inter_closure
import Submission.Work.Repel.invFunOn_differentiableOn
import Submission.Work.HornTopo.horn_topo
import Submission.Work.Horn.HB.Phi_component_proper
import Submission.Work.Horn.HB.E_component_proper

/-! Guidance from the project lead (the requester):

LEAD DESIGN (read Submission/Work/Horn/HB/DESIGN.md). Piece HB3: LF_v for g = pushdown d.E at
v = piExp (Φ c), from sibling HB2 (Work.Horn.HB.E_component_proper; import it).

## The formalisation used here (2026-10-03)

HB2 is consumed in the hypothesis form `hHB2` of `pushdown_LF_of_components` below (= the statement
of `Submission/Work/Horn/HB/E_component_proper_of_Phi.lean`; that file proves HB2 from the sibling
`.../Phi_component_proper_of_bounded.lean`).  The transfer to the `x`-plane is proved here and uses

* `isCompact_componentIn_preimage`, an abstract (purely set-theoretic) fact: if `f : ℂ → ℂ` is
  "proper over `Ω`" on `B` and `U ⊆ Ω`, then every connected component of `B ∩ f ⁻¹' U` is proper
  over `U` (proof: `connectedComponentIn = (B ∩ f ⁻¹' U) ∩ closure (component)`);
* `isCompact_blob`, compactness of the `w`-plane blob `ball z s ∩ π ⁻¹' S` over a compact
  `S ⊆ π '' ball z s`;
* `π '' C̃ = C_x`, proved by a *clopen* argument: `π '' C̃` is open, and closed in `U_x` because a
  limit point lifts into `Ã` and the translates `Ã + k` (`k ≠ 0`) are disjoint from `Ã`.

No continuity of `pushdown d.E` on its domain is needed anywhere.
-/

namespace Work.Horn.HB

open MandelDim Set Metric Filter Topology
open scoped Topology

noncomputable section

/-- An integer whose image in `ℂ` has norm `< 1` is `0`. -/
private lemma int_eq_zero_of_norm_lt_one {m : ℤ} (h : ‖(m : ℂ)‖ < 1) : m = 0 := by
  have h2 : |(m : ℝ)| < 1 := by
    simpa [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im] using h
  rw [abs_lt] at h2
  have h1 : (-1 : ℤ) < m := by exact_mod_cast h2.1
  have h4 : m < 1 := by exact_mod_cast h2.2
  omega

/-- `π` is injective on a ball of radius `s` when `2 s ≤ 1`. -/
private lemma piExp_injOn_ball {z : ℂ} {s : ℝ} (hs : 2 * s ≤ 1) :
    Set.InjOn MandelDim.piExp (Metric.ball z s) := by
  intro u hu u' hu' huv
  obtain ⟨m, hm⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp huv
  have hEq : u - u' = (m : ℂ) := by rw [hm]; ring
  have hlt : ‖(m : ℂ)‖ < 1 := by
    rw [← hEq]
    have h1 : ‖u - u'‖ ≤ ‖u - z‖ + ‖z - u'‖ := by
      rw [show u - u' = (u - z) + (z - u') by ring]
      exact norm_add_le _ _
    have h2 : ‖u - z‖ < s := by simpa [dist_eq_norm] using hu
    have h3 : ‖z - u'‖ < s := by rw [norm_sub_rev]; simpa [dist_eq_norm] using hu'
    linarith
  have hm0 : m = 0 := int_eq_zero_of_norm_lt_one hlt
  simp only [hm0, Int.cast_zero, add_zero] at hm
  exact hm

/-- **The `w`-plane blob over a compact set is compact.**  For `S ⊆ π '' ball z s` compact, the
preimage `ball z s ∩ π ⁻¹' S` is compact: it is the image of `S` under the local inverse branch of
`π`, which is holomorphic on `π '' ball z s`. -/
private lemma isCompact_blob {z : ℂ} {s : ℝ} (hs : 2 * s ≤ 1) {S : Set ℂ}
    (hS : IsCompact S) (hSsub : S ⊆ MandelDim.piExp '' Metric.ball z s) :
    IsCompact (Metric.ball z s ∩ MandelDim.piExp ⁻¹' S) := by
  have hinj : Set.InjOn MandelDim.piExp (Metric.ball z s) := piExp_injOn_ball hs
  have hdiff : DifferentiableOn ℂ MandelDim.piExp (Metric.ball z s) :=
    (by unfold MandelDim.piExp; fun_prop : Differentiable ℂ MandelDim.piExp).differentiableOn
  have hfdiff : DifferentiableOn ℂ (Function.invFunOn MandelDim.piExp (Metric.ball z s))
      (MandelDim.piExp '' Metric.ball z s) :=
    Work.Repel.invFunOn_differentiableOn Metric.isOpen_ball hinj hdiff
  have himg : Function.invFunOn MandelDim.piExp (Metric.ball z s) '' S
      = Metric.ball z s ∩ MandelDim.piExp ⁻¹' S := by
    ext y; constructor
    · rintro ⟨a, ha, rfl⟩
      have hex : ∃ x ∈ Metric.ball z s, MandelDim.piExp x = a := hSsub ha
      refine ⟨Function.invFunOn_mem hex, ?_⟩
      rw [Set.mem_preimage, Function.invFunOn_eq hex]
      exact ha
    · intro hy
      refine ⟨MandelDim.piExp y, hy.2, ?_⟩
      have hex : ∃ x ∈ Metric.ball z s, MandelDim.piExp x = MandelDim.piExp y :=
        ⟨y, hy.1, rfl⟩
      exact hinj (Function.invFunOn_mem hex) hy.1 (Function.invFunOn_eq hex)
  rw [← himg]
  exact hS.image_of_continuousOn (hfdiff.continuousOn.mono hSsub)

/-- **Abstract properness of components.**  If `f : ℂ → ℂ` is proper over `Ω` on `B` (preimages of
compacts of `Ω` are compact) and `U ⊆ Ω`, then every connected component of `B ∩ f ⁻¹' U` is proper
over `U`. -/
private lemma isCompact_componentIn_preimage {f : ℂ → ℂ} {B Ω U : Set ℂ}
    (hUΩ : U ⊆ Ω) (hprop : ∀ L ⊆ Ω, IsCompact L → IsCompact (B ∩ f ⁻¹' L))
    {x : ℂ} (hx : x ∈ B ∩ f ⁻¹' U) :
    ∀ K ⊆ U, IsCompact K →
      IsCompact (connectedComponentIn (B ∩ f ⁻¹' U) x ∩ f ⁻¹' K) := by
  intro K hKU hKc
  have hcl : connectedComponentIn (B ∩ f ⁻¹' U) x
      = (B ∩ f ⁻¹' U) ∩ closure (connectedComponentIn (B ∩ f ⁻¹' U) x) :=
    Work.BasinSC.Tower.connectedComponentIn_inter_closure
  have hset : connectedComponentIn (B ∩ f ⁻¹' U) x ∩ f ⁻¹' K
      = (B ∩ f ⁻¹' K) ∩ closure (connectedComponentIn (B ∩ f ⁻¹' U) x) := by
    ext y; constructor
    · intro hy
      obtain ⟨hyC, hyK⟩ := hy
      exact ⟨⟨(connectedComponentIn_subset _ _ hyC).1, hyK⟩, subset_closure hyC⟩
    · intro hy
      obtain ⟨⟨hyB, hyK⟩, hycl⟩ := hy
      refine ⟨?_, hyK⟩
      rw [hcl]
      exact ⟨⟨hyB, hKU hyK⟩, hycl⟩
  rw [hset]
  exact (hprop K (hKU.trans hUΩ) hKc).inter_right isClosed_closure

/-- **HB3, conditional on HB2.**  This is the target statement with the conclusion of the sibling
piece HB2 (`Submission/Work/Horn/HB/E_component_proper_of_Phi.lean`) taken as a hypothesis. -/
private theorem pushdown_LF_of_components {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}
    (d : MandelDim.ParabData f₀ D₀) (hS : MandelDim.IsF0Setup f₀ D₀ B c)
    (hHB2 : ∃ ρ > 0, ρ < 1 / 2 ∧
      ∀ w ∈ MandelDim.BuOf d B ∪ MandelDim.BlOf d B, d.E w ∈ Metric.ball (d.Φ c) ρ →
        ∀ K ⊆ Metric.ball (d.Φ c) ρ, IsCompact K →
          IsCompact (connectedComponentIn
            ((MandelDim.BuOf d B ∪ MandelDim.BlOf d B) ∩
              d.E ⁻¹' Metric.ball (d.Φ c) ρ) w ∩ d.E ⁻¹' K)) :
    ∃ r > 0, r < ‖MandelDim.piExp (d.Φ c)‖ ∧
      ∀ x ∈ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)),
        MandelDim.pushdown d.E x ∈ Metric.ball (MandelDim.piExp (d.Φ c)) r →
        ∀ K ⊆ Metric.ball (MandelDim.piExp (d.Φ c)) r, IsCompact K →
          IsCompact (connectedComponentIn
            (insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)) ∩
              MandelDim.pushdown d.E ⁻¹' Metric.ball (MandelDim.piExp (d.Φ c)) r) x ∩
            MandelDim.pushdown d.E ⁻¹' K) := by
  classical
  obtain ⟨hBuO, hBlO, hBuT, hBlT, _hUp, _hLo, hDE⟩ :=
    Work.HornTopo.horn_topo f₀ D₀ B c d hS
  -- ## the `w`-plane end set `Y = B̃ᵘ ∪ B̃ˡ`
  set Y : Set ℂ := MandelDim.BuOf d B ∪ MandelDim.BlOf d B with hY
  have hYmem : ∀ z : ℂ, z ∈ Y ↔ z ∈ MandelDim.BuOf d B ∨ z ∈ MandelDim.BlOf d B := by
    intro z; simp only [hY, Set.mem_union]
  have hYO : IsOpen Y := by rw [hY]; exact hBuO.union hBlO
  have hYT : MandelDim.IsTInvariant Y := by
    intro w; rw [hYmem w, hYmem (w + 1), hBuT w, hBlT w]
  have hYE : ∀ w ∈ Y, w + 1 ∈ Y → d.E (w + 1) = d.E w + 1 := fun w hw hw1 =>
    MandelDim.ParabData.E_add_one d (hDE ((hYmem w).mp hw)) (hDE ((hYmem (w + 1)).mp hw1))
  have hEcont : ContinuousOn d.E Y := by
    have hsub : Y ⊆ d.Dφ := fun w hw => (hDE ((hYmem w).mp hw)).1
    have hdiff : DifferentiableOn ℂ d.E Y :=
      d.Φ_holo.comp (d.φ_holo.mono hsub) (fun w hw => (hDE ((hYmem w).mp hw)).2)
    exact hdiff.continuousOn
  have hYT_int : ∀ (w : ℂ) (k : ℤ), w + (k : ℂ) ∈ Y ↔ w ∈ Y := by
    intro w k
    constructor
    · intro h
      have h' := Work.Horn.MandelDim.IsTInvariant.add_int hYT h (-k)
      rwa [show w + (k : ℂ) + (((-k : ℤ)) : ℂ) = w by push_cast; ring] at h'
    · intro h
      exact Work.Horn.MandelDim.IsTInvariant.add_int hYT h k
  -- ## HB2 and the choice of the radii `ρ` (given) and `r`
  obtain ⟨ρ, hρ0, hρhalf, hHB2raw⟩ := hHB2
  have hHB2 : ∀ w ∈ Y, d.E w ∈ Metric.ball (d.Φ c) ρ →
      ∀ K ⊆ Metric.ball (d.Φ c) ρ, IsCompact K →
        IsCompact (connectedComponentIn (Y ∩ d.E ⁻¹' Metric.ball (d.Φ c) ρ) w ∩
          d.E ⁻¹' K) := by
    intro w hw hwE K hK hKc
    simpa only [hY] using hHB2raw w ((hYmem w).mpr hw) hwE K hK hKc
  have h2ρ : 2 * ρ ≤ 1 := by linarith
  have hvne : MandelDim.piExp (d.Φ c) ≠ 0 := Work.Horn.MandelDim.piExp_ne_zero _
  have hvpos : 0 < ‖MandelDim.piExp (d.Φ c)‖ := norm_pos_iff.mpr hvne
  have hπcont : Continuous MandelDim.piExp := Work.Horn.piExp_continuous
  have hπopen : IsOpenMap MandelDim.piExp := Work.Horn.piExp_isOpenMap
  obtain ⟨r, hr0, hr_lt, hrsub⟩ :
      ∃ r : ℝ, 0 < r ∧ r < ‖MandelDim.piExp (d.Φ c)‖ ∧
        Metric.ball (MandelDim.piExp (d.Φ c)) r ⊆ MandelDim.piExp '' Metric.ball (d.Φ c) ρ := by
    have hmem : MandelDim.piExp '' Metric.ball (d.Φ c) ρ ∈ nhds (MandelDim.piExp (d.Φ c)) :=
      (hπopen _ Metric.isOpen_ball).mem_nhds ⟨d.Φ c, Metric.mem_ball_self hρ0, rfl⟩
    obtain ⟨r₀, hr₀pos, hr₀sub⟩ := Metric.mem_nhds_iff.mp hmem
    refine ⟨min r₀ (‖MandelDim.piExp (d.Φ c)‖ / 2), lt_min hr₀pos (by positivity), ?_, ?_⟩
    · have h1 : min r₀ (‖MandelDim.piExp (d.Φ c)‖ / 2) ≤ ‖MandelDim.piExp (d.Φ c)‖ / 2 :=
        min_le_right _ _
      linarith
    · exact (Metric.ball_subset_ball (min_le_left _ _)).trans hr₀sub
  refine ⟨r, hr0, hr_lt, ?_⟩
  intro x hxmem hgx K hKsub hKc
  have h0ball : (0 : ℂ) ∉ Metric.ball (MandelDim.piExp (d.Φ c)) r := by
    simp only [Metric.mem_ball, dist_eq_norm, zero_sub, norm_neg]
    exact not_lt.mpr hr_lt.le
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, Work.Horn.MandelDim.pushdown_zero] at hgx
    exact h0ball hgx
  obtain ⟨w₀, hw₀Y, hw₀x⟩ : ∃ w₀ ∈ Y, MandelDim.piExp w₀ = x := by
    rcases hxmem with h | h
    · exact absurd h hx0
    · exact h
  -- ## the `w`-plane blob `Ũ` and the lift decomposition
  set Uh : Set ℂ := Metric.ball (d.Φ c) ρ ∩
    MandelDim.piExp ⁻¹' Metric.ball (MandelDim.piExp (d.Φ c)) r with hUh
  have hUhmem : ∀ z : ℂ, z ∈ Uh ↔ z ∈ Metric.ball (d.Φ c) ρ ∧
      MandelDim.piExp z ∈ Metric.ball (MandelDim.piExp (d.Φ c)) r := by
    intro z; simp only [hUh, Set.mem_inter_iff, Set.mem_preimage]
  have hUhopen : IsOpen Uh := by
    rw [hUh]; exact Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage hπcont)
  have hπUh : MandelDim.piExp '' Uh = Metric.ball (MandelDim.piExp (d.Φ c)) r := by
    rw [hUh, Set.image_inter_preimage]
    exact Set.inter_eq_right.mpr hrsub
  have hpre_ball : ∀ z : ℂ, MandelDim.piExp z ∈ Metric.ball (MandelDim.piExp (d.Φ c)) r ↔
      ∃ k : ℤ, z + (k : ℂ) ∈ Uh := by
    intro z
    constructor
    · intro hz
      obtain ⟨β, hβℬ, hβ⟩ := hrsub hz
      obtain ⟨m, hm⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp hβ
      refine ⟨m, ?_⟩
      have hzm : z + (m : ℂ) = β := hm.symm
      rw [hzm]
      exact ⟨hβℬ, by rw [Set.mem_preimage, hβ]; exact hz⟩
    · rintro ⟨k, hk⟩
      have hper : MandelDim.piExp (z + (k : ℂ)) = MandelDim.piExp z :=
        Work.Horn.MandelDim.piExp_add_intCast z k
      rw [← hper]
      exact ((hUhmem _).mp hk).2
  have hEw₀ : MandelDim.piExp (d.E w₀) ∈ Metric.ball (MandelDim.piExp (d.Φ c)) r := by
    have h := Work.Horn.MandelDim.pushdown_piExp (E := d.E) hYT hYE hw₀Y
    rw [hw₀x] at h
    rwa [h] at hgx
  obtain ⟨k₀, hk₀⟩ := (hpre_ball (d.E w₀)).mp hEw₀
  set w : ℂ := w₀ + (k₀ : ℂ) with hwdef
  have hwY : w ∈ Y := by
    rw [hwdef]; exact (hYT_int w₀ k₀).mpr hw₀Y
  have hwπ : MandelDim.piExp w = x := by
    rw [hwdef, Work.Horn.MandelDim.piExp_add_intCast w₀ k₀]; exact hw₀x
  have hwE : d.E w ∈ Uh := by
    rw [hwdef, Work.Horn.MandelDim.E_add_int (E := d.E) hYT hYE hw₀Y k₀]
    exact hk₀
  have hwEℬ : d.E w ∈ Metric.ball (d.Φ c) ρ := ((hUhmem _).mp hwE).1
  -- ## the `w`-plane component
  set Ah : Set ℂ := Y ∩ d.E ⁻¹' Uh with hAh
  have hAhmem : ∀ z : ℂ, z ∈ Ah ↔ z ∈ Y ∧ d.E z ∈ Uh := by
    intro z; simp only [hAh, Set.mem_inter_iff, Set.mem_preimage]
  have hAhopen : IsOpen Ah := by
    rw [hAh]; exact hEcont.isOpen_inter_preimage hYO hUhopen
  have hwAh : w ∈ Ah := (hAhmem w).mpr ⟨hwY, hwE⟩
  set Ctil : Set ℂ := connectedComponentIn Ah w with hCtil
  have hCtilsub : Ctil ⊆ Ah := connectedComponentIn_subset _ _
  have hCtilopen : IsOpen Ctil := by rw [hCtil]; exact hAhopen.connectedComponentIn
  have hCtilcl : Ctil = Ah ∩ closure Ctil := by
    rw [hCtil]; exact Work.BasinSC.Tower.connectedComponentIn_inter_closure
  have hCtilY : ∀ z ∈ Ctil, z ∈ Y := fun z hz => ((hAhmem z).mp (hCtilsub hz)).1
  have hCtilE : ∀ z ∈ Ctil, d.E z ∈ Uh := fun z hz => ((hAhmem z).mp (hCtilsub hz)).2
  -- disjointness of the translates of `Uh` (hence of `Ah`)
  have hUhshift : ∀ (m : ℤ) (u : ℂ), u ∈ Uh → u + (m : ℂ) ∈ Uh → m = 0 := by
    intro m u hu hu'
    have huℬ : u ∈ Metric.ball (d.Φ c) ρ := ((hUhmem u).mp hu).1
    have hu'ℬ : u + (m : ℂ) ∈ Metric.ball (d.Φ c) ρ := ((hUhmem (u + (m : ℂ))).mp hu').1
    have hlt : ‖(m : ℂ)‖ < 1 := by
      have hEq : (m : ℂ) = (u + (m : ℂ)) - u := by ring
      rw [hEq]
      have h1 : ‖(u + (m : ℂ)) - u‖ ≤ ‖(u + (m : ℂ)) - d.Φ c‖ + ‖d.Φ c - u‖ := by
        rw [show (u + (m : ℂ)) - u = ((u + (m : ℂ)) - d.Φ c) + (d.Φ c - u) by ring]
        exact norm_add_le _ _
      have h2 : ‖(u + (m : ℂ)) - d.Φ c‖ < ρ := by simpa [dist_eq_norm] using hu'ℬ
      have h3 : ‖d.Φ c - u‖ < ρ := by rw [norm_sub_rev]; simpa [dist_eq_norm] using huℬ
      linarith
    exact int_eq_zero_of_norm_lt_one hlt
  have hAhdisj : ∀ (m : ℤ), m ≠ 0 → ∀ z ∈ Ah, z + (m : ℂ) ∉ Ah := by
    intro m hm z hz hz'
    have h1 : d.E z ∈ Uh := ((hAhmem z).mp hz).2
    have h2 : d.E (z + (m : ℂ)) ∈ Uh := ((hAhmem (z + (m : ℂ))).mp hz').2
    have hEeq : d.E (z + (m : ℂ)) = d.E z + (m : ℂ) :=
      Work.Horn.MandelDim.E_add_int (E := d.E) hYT hYE ((hAhmem z).mp hz).1 m
    rw [hEeq] at h2
    exact hm (hUhshift m (d.E z) h1 h2)
  -- ## `π '' Ah = U_x`
  set Ux : Set ℂ := insert 0 (MandelDim.piExp '' Y) ∩
      MandelDim.pushdown d.E ⁻¹' Metric.ball (MandelDim.piExp (d.Φ c)) r with hUx
  have hUxmem : ∀ z : ℂ, z ∈ Ux ↔ z ∈ insert 0 (MandelDim.piExp '' Y) ∧
      MandelDim.pushdown d.E z ∈ Metric.ball (MandelDim.piExp (d.Φ c)) r := by
    intro z; simp only [hUx, Set.mem_inter_iff, Set.mem_preimage]
  have hπAh : MandelDim.piExp '' Ah = Ux := by
    ext y; constructor
    · rintro ⟨z, hzAh, rfl⟩
      obtain ⟨hzY, hzUh⟩ := (hAhmem z).mp hzAh
      refine (hUxmem _).mpr ⟨Set.mem_insert_of_mem _ ⟨z, hzY, rfl⟩, ?_⟩
      rw [Work.Horn.MandelDim.pushdown_piExp (E := d.E) hYT hYE hzY]
      exact ((hUhmem _).mp hzUh).2
    · intro hy
      obtain ⟨hyD, hyg⟩ := (hUxmem y).mp hy
      rcases hyD with h0 | hY'
      · rw [h0, Work.Horn.MandelDim.pushdown_zero] at hyg
        exact absurd hyg h0ball
      · obtain ⟨z, hzY, hzx⟩ := hY'
        have hEz : MandelDim.piExp (d.E z) ∈ Metric.ball (MandelDim.piExp (d.Φ c)) r := by
          have h := Work.Horn.MandelDim.pushdown_piExp (E := d.E) hYT hYE hzY
          rw [hzx] at h
          rw [h] at hyg; exact hyg
        obtain ⟨k, hk⟩ := (hpre_ball (d.E z)).mp hEz
        refine ⟨z + (k : ℂ), (hAhmem _).mpr ⟨?_, ?_⟩, ?_⟩
        · exact (hYT_int z k).mpr hzY
        · have h := Work.Horn.MandelDim.E_add_int (E := d.E) hYT hYE hzY k
          rw [h]; exact hk
        · rw [Work.Horn.MandelDim.piExp_add_intCast z k]; exact hzx
  -- ## `π '' Ctil` is closed in `U_x`
  have hclosed : ∀ y ∈ Ux, y ∈ closure (MandelDim.piExp '' Ctil) →
      y ∈ MandelDim.piExp '' Ctil := by
    intro y hyU hycl
    obtain ⟨z, hzAh, hzy⟩ : ∃ z ∈ Ah, MandelDim.piExp z = y := by
      have hy' : y ∈ MandelDim.piExp '' Ah := by rw [hπAh]; exact hyU
      exact hy'
    obtain ⟨sz, hszpos, hszsub⟩ := Metric.isOpen_iff.mp hAhopen z hzAh
    set s : ℝ := min sz (1 / 4) with hsdef
    have hspos : 0 < s := lt_min hszpos (by norm_num)
    have hs2 : 2 * s ≤ 1 := by have h1 : s ≤ 1 / 4 := min_le_right _ _; linarith
    have hsinj : Set.InjOn MandelDim.piExp (Metric.ball z s) := piExp_injOn_ball hs2
    have hssubAh : Metric.ball z s ⊆ Ah := fun u hu =>
      hszsub (Metric.ball_subset_ball (min_le_left _ _) hu)
    have hzcl : z ∈ closure Ctil := by
      rw [_root_.mem_closure_iff]
      intro O hO hzO
      obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hzO)
      set s' : ℝ := min δ s with hs'def
      have hs'pos : 0 < s' := lt_min hδpos hspos
      have hs'subδ : Metric.ball z s' ⊆ O :=
        (Metric.ball_subset_ball (min_le_left _ _)).trans hδsub
      have hs'subs : Metric.ball z s' ⊆ Metric.ball z s :=
        Metric.ball_subset_ball (min_le_right _ _)
      have hs'subAh : Metric.ball z s' ⊆ Ah := hs'subs.trans hssubAh
      have hne := (_root_.mem_closure_iff.mp hycl) (MandelDim.piExp '' Metric.ball z s')
        (hπopen _ Metric.isOpen_ball) ⟨z, Metric.mem_ball_self hs'pos, hzy⟩
      obtain ⟨c, hcimg, hcCtil⟩ := hne
      obtain ⟨d, hdball, hdc⟩ := hcimg
      obtain ⟨c', hc'Ctil, hc'c⟩ := hcCtil
      have hcd : c' = d := by
        obtain ⟨k, hk⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp (hc'c.trans hdc.symm)
        rcases eq_or_ne k 0 with hk0 | hk0
        · simp only [hk0, Int.cast_zero, add_zero] at hk; exact hk
        · exfalso
          exact (hAhdisj k hk0 d (hs'subAh hdball)) (hk ▸ (hCtilsub hc'Ctil))
      exact ⟨c', hcd.symm ▸ (hs'subδ hdball), hc'Ctil⟩
    have hzCtil : z ∈ Ctil := by
      rw [hCtilcl]; exact ⟨hzAh, hzcl⟩
    exact ⟨z, hzCtil, hzy⟩
  -- ## `C_x = π '' Ctil`
  have hxCx : x ∈ connectedComponentIn Ux x := mem_connectedComponentIn ⟨hxmem, hgx⟩
  have hxπCtil : x ∈ MandelDim.piExp '' Ctil :=
    ⟨w, mem_connectedComponentIn hwAh, hwπ⟩
  have hCxsubUx : connectedComponentIn Ux x ⊆ Ux := connectedComponentIn_subset _ _
  have hCxCtil : connectedComponentIn Ux x ⊆ MandelDim.piExp '' Ctil :=
    isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
      (hπopen _ hCtilopen) ⟨x, hxCx, hxπCtil⟩
      (fun y hy => hclosed y (hCxsubUx hy.2) hy.1)
  have hCtilCx : MandelDim.piExp '' Ctil ⊆ connectedComponentIn Ux x := by
    have hpre : IsPreconnected (MandelDim.piExp '' Ctil) :=
      isPreconnected_connectedComponentIn.image _ hπcont.continuousOn
    refine hpre.subset_connectedComponentIn ⟨w, mem_connectedComponentIn hwAh, hwπ⟩ ?_
    rintro y ⟨z, hzCtil, rfl⟩
    refine (hUxmem _).mpr ⟨Set.mem_insert_of_mem _ ⟨z, hCtilY z hzCtil, rfl⟩, ?_⟩
    rw [Work.Horn.MandelDim.pushdown_piExp (E := d.E) hYT hYE (hCtilY z hzCtil)]
    exact ((hUhmem _).mp (hCtilE z hzCtil)).2
  have hCxpi : connectedComponentIn Ux x = MandelDim.piExp '' Ctil :=
    subset_antisymm hCxCtil hCtilCx
  -- ## compactness transfer
  set Kh : Set ℂ := Metric.ball (d.Φ c) ρ ∩ MandelDim.piExp ⁻¹' K with hKh
  have hKhmem : ∀ z : ℂ, z ∈ Kh ↔ z ∈ Metric.ball (d.Φ c) ρ ∧ MandelDim.piExp z ∈ K := by
    intro z; simp only [hKh, Set.mem_inter_iff, Set.mem_preimage]
  have hKhsub : Kh ⊆ Metric.ball (d.Φ c) ρ := fun z hz => ((hKhmem z).mp hz).1
  have hKhc : IsCompact Kh := by
    rw [hKh]
    exact isCompact_blob h2ρ hKc (hKsub.trans hrsub)
  set Cp : Set ℂ := connectedComponentIn (Y ∩ d.E ⁻¹' Metric.ball (d.Φ c) ρ) w with hCp
  have hCpsub : Cp ⊆ Y ∩ d.E ⁻¹' Metric.ball (d.Φ c) ρ := connectedComponentIn_subset _ _
  have hwCp : w ∈ Cp := mem_connectedComponentIn ⟨hwY, hwEℬ⟩
  have hCtilCp : Ctil ⊆ Cp := by
    refine (isPreconnected_connectedComponentIn (F := Ah) (x := w)).subset_connectedComponentIn
      (mem_connectedComponentIn hwAh) ?_
    intro u hu
    obtain ⟨huY, huUh⟩ := (hAhmem u).mp (hCtilsub hu)
    exact ⟨huY, ((hUhmem (d.E u)).mp huUh).1⟩
  have hCtileq : Ctil = connectedComponentIn (Cp ∩ d.E ⁻¹' Uh) w := by
    refine subset_antisymm ?_ ?_
    · refine (isPreconnected_connectedComponentIn (F := Ah) (x := w)).subset_connectedComponentIn
        (mem_connectedComponentIn hwAh) ?_
      intro u hu
      exact ⟨hCtilCp hu, hCtilE u hu⟩
    · refine (isPreconnected_connectedComponentIn (F := Cp ∩ d.E ⁻¹' Uh) (x := w)).subset_connectedComponentIn
        (mem_connectedComponentIn ⟨hwCp, hwE⟩) ?_
      intro u hu
      obtain ⟨hu1, hu2⟩ := connectedComponentIn_subset (Cp ∩ d.E ⁻¹' Uh) w hu
      exact (hAhmem u).mpr ⟨(hCpsub hu1).1, hu2⟩
  have hcomptil : IsCompact (Ctil ∩ d.E ⁻¹' Kh) := by
    have hKhUh : Kh ⊆ Uh := fun z hz => (hUhmem z).mpr
      ⟨hKhsub hz, hKsub ((hKhmem z).mp hz).2⟩
    rw [hCtileq]
    exact isCompact_componentIn_preimage (f := d.E) (B := Cp) (Ω := Metric.ball (d.Φ c) ρ)
      (U := Uh) (x := w) (fun u hu => ((hUhmem u).mp hu).1)
      (fun L hL hLc => hHB2 w hwY hwEℬ L hL hLc)
      ⟨hwCp, hwE⟩ Kh hKhUh hKhc
  have hset : connectedComponentIn Ux x ∩ MandelDim.pushdown d.E ⁻¹' K =
      MandelDim.piExp '' (Ctil ∩ d.E ⁻¹' Kh) := by
    rw [hCxpi]
    ext y; constructor
    · rintro ⟨hy, hyg⟩
      obtain ⟨z, hzCtil, rfl⟩ := hy
      refine ⟨z, ⟨hzCtil, ?_⟩, rfl⟩
      rw [Set.mem_preimage] at hyg
      rw [Work.Horn.MandelDim.pushdown_piExp (E := d.E) hYT hYE (hCtilY z hzCtil)] at hyg
      exact (hKhmem _).mpr ⟨((hUhmem _).mp (hCtilE z hzCtil)).1, hyg⟩
    · rintro ⟨z, ⟨hzCtil, hzKh⟩, rfl⟩
      refine ⟨⟨z, hzCtil, rfl⟩, ?_⟩
      rw [Set.mem_preimage, Work.Horn.MandelDim.pushdown_piExp (E := d.E) hYT hYE (hCtilY z hzCtil)]
      exact ((hKhmem (d.E z)).mp hzKh).2
  rw [hset]
  exact hcomptil.image_of_continuousOn (hπcont.continuousOn.mono (Set.subset_univ _))

/-- **HB3 / LF at the critical value.** -/
theorem pushdown_LF {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hS : MandelDim.IsF0Setup f₀ D₀ B c) :
    ∃ r > 0, r < ‖MandelDim.piExp (d.Φ c)‖ ∧
      ∀ x ∈ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)),
        MandelDim.pushdown d.E x ∈ Metric.ball (MandelDim.piExp (d.Φ c)) r →
        ∀ K ⊆ Metric.ball (MandelDim.piExp (d.Φ c)) r, IsCompact K →
          IsCompact (connectedComponentIn
            (insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)) ∩
              MandelDim.pushdown d.E ⁻¹' Metric.ball (MandelDim.piExp (d.Φ c)) r) x ∩
            MandelDim.pushdown d.E ⁻¹' K) :=
  pushdown_LF_of_components d hS
    ⟨1 / 4, by norm_num, by norm_num, fun w hw hwE K hK hKc =>
      E_component_proper_of_hPhi d hS
        (fun U' hU'o hU'c hU'b z hzB hzU => Phi_component_proper d hS hU'o hU'c hU'b hzB hzU)
        (by norm_num) (by norm_num) hw hwE K hK hKc⟩

end

end Work.Horn.HB
