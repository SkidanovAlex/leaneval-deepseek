import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.GoodDrawingFamily
import Submission.Work.Drive.N2.wideCollar
import Submission.Work.Drive.N2C.levelCurves_exists_transition
import Submission.Work.Drive.N2C.canonicalReparamIso
import Submission.Work.Drive.N2C.shellFlip
import Submission.Work.Drive.N2C.roundToRoundIso
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2C.isotopyCalc
import Submission.Work.Drive.N2C.levelCurvesTransportExplicit
import Submission.Work.Drive.N2C.isLevelIsotopy_blend
import Submission.Work.Drive.N2C.isLevelIsotopy_transport
import Submission.Work.Drive.N2C.isLevelIsotopy_windowMovie
import Submission.Work.Drive.N2.roundConfigPictureGlobal
import Submission.Work.Drive.N2.roundConfigPath

/-!
# H7: the gap engine (the analytic core of Tier C1)

`Work.Drive.N2C.gapDrawing_of_certifiedEnds` (C1) says: given two good drawings `g₁`, `g₂` of the two
*ends* of a critical-free value slab, each carrying a certificate at a level just inside the slab, they
transport to a single good drawing `G` of the whole slab which agrees with `g₁` and `g₂` on the two
collars.  This file proves it as `Work.Drive.N2C.H7.gapDrawing_of_certifiedEnds` (a private namespace,
so that it can coexist with the holder at the public path), **for a compact surface**: the round-to-round
isotopy (B7) it uses needs `T2Space`, `SecondCountableTopology` and `CompactSpace`, which the public
holder's statement omits.

The construction is the five-piece level isotopy at the anchor level `b := (m₁ + m₂)/2`:

* `E₁ s y = g₁ (Φ (ρ₁ s - b, y))`       — the `g₁`-end (B5), `ρ₁` the identity on the lower collar;
* `E₂ s y = e₁' s (Φ (u₁ - b, y))`      — the certificate at `u₁` transported to `b` (B4);
* `E₃`                                   — round-to-round at `b` (B7), through the *transported*
                                           parametrisations (A2 with the parametrisation exposed);
* `E₄ s y = e₂' (1 - s) (Φ (u₂ - b, y))` — the certificate at `u₂`, reversed, transported to `b`;
* `E₅ s y = g₂ (Φ (ρ₂ s - b, y))`       — the `g₂`-end, `ρ₂` the identity on the upper collar.

Each piece is flattened near its junction times (B1's time reparametrisation) so that consecutive
pieces agree on a whole interval, and the five are concatenated (B3).  The resulting family `e` at `b`
gives the drawing `G z = e (f z) (Φ (b - f z, z))` through the **wide** collar drawing
(`Work.Drive.N2.collarDrawing_wide`: the anchor `b` lies in the *interior* of the slab, which the
shipped `collarDrawing_local` does not allow).  The two agreements are then the flow identity
`Φ (u - b, Φ (b - f z, z)) = z` at the values `u = f z` of the two collars, where the corresponding
time maps `ρ₁`, `ρ₂` are the identity.
-/

namespace Work.Drive.N2C.H7

open scoped Manifold ContDiff Topology
open Set Filter

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-! ## Smooth steps -/

/-- The smooth step `0` below `u`, `1` above `v` (for `u < v`). -/
noncomputable def smoothStep (u v : ℝ) : ℝ → ℝ :=
  fun s => Real.smoothTransition ((s - u) / (v - u))

lemma smoothStep_contDiff (u v : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (smoothStep u v) := by
  unfold smoothStep
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

lemma smoothStep_zero (u v : ℝ) (h : u < v) {s : ℝ} (hs : s ≤ u) : smoothStep u v s = 0 := by
  unfold smoothStep
  refine Real.smoothTransition.zero_of_nonpos ?_
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

lemma smoothStep_one (u v : ℝ) (h : u < v) {s : ℝ} (hs : v ≤ s) : smoothStep u v s = 1 := by
  unfold smoothStep
  refine Real.smoothTransition.one_of_one_le ?_
  rw [one_le_div (by linarith)]
  linarith

lemma smoothStep_mem (u v : ℝ) (s : ℝ) : smoothStep u v s ∈ Set.Icc 0 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-! ## Reversing a level isotopy in time -/

theorem isLevelIsotopy_rev' {f : M → ℝ} {b : ℝ} {e : ℝ → M → EuclideanSpace ℝ (Fin 3)}
    (he : IsLevelIsotopy f b e) :
    IsLevelIsotopy f b (fun s y => e (1 - s) y) := by
  simpa using isLevelIsotopy_comp_time he (ρ := fun s : ℝ => 1 - s) (by fun_prop)


/-- A convex combination lies between its two ends. -/
lemma convex_mem_Icc {a b γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    (1 - γ) * a + γ * b ∈ Set.Icc (min a b) (max a b) := by
  constructor
  · have h1' : (1 - γ) * min a b ≤ (1 - γ) * a :=
      mul_le_mul_of_nonneg_left (min_le_left a b) (by linarith)
    have h2' : γ * min a b ≤ γ * b := mul_le_mul_of_nonneg_left (min_le_right a b) h0
    have hsum : (1 - γ) * min a b + γ * min a b = min a b := by ring
    linarith
  · have h1' : (1 - γ) * a ≤ (1 - γ) * max a b :=
      mul_le_mul_of_nonneg_left (le_max_left a b) (by linarith)
    have h2' : γ * b ≤ γ * max a b := mul_le_mul_of_nonneg_left (le_max_right a b) h0
    have hsum : (1 - γ) * max a b + γ * max a b = max a b := by ring
    linarith

/-- **DEVELOPMENT STUB** (to be replaced by the Tier B round-to-round isotopy as soon as that lane
lands it — it was refactored into pieces on 2026-09-27, see
`Submission/Work/Drive/N2C/NOTES_H7j_E1_and_C1_DONE_LAST_MILE.md` §4).  Statement copied verbatim from
the design (`N2Lead/NOTES_LEAD_coherentWindows.md` §4, Tier B7). -/
theorem roundToRound_dev [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) {b : ℝ}
    (hreg : ∀ x : M, f x = b → ¬ Work.Drive.Morse.IsCritical f x)
    {n n' : ℕ} (L : LevelCurves f b n) (L' : LevelCurves f b n')
    (D : Work.Drive.N2.RoundConfig n) (D' : Work.Drive.N2.RoundConfig n')
    (hD : D.Disjoint) (hD' : D'.Disjoint) :
    ∃ e : ℝ → M → EuclideanSpace ℝ (Fin 3), IsLevelIsotopy f b e ∧
      (∀ (i : Fin n) (x : ℝ), e 0 (L.γ i x) = D.circle i x) ∧
      (∀ (i : Fin n') (x : ℝ), e 1 (L'.γ i x) = D'.circle i x) := by
  obtain ⟨σ, ε, hh, hσ, hε, hcd, hper, hmono, hrel⟩ :=
    Work.Drive.N2C.levelCurves_exists_transition (f := f) hf hreg L L'
  have hnn : n' = n := by
    have hcard : Fintype.card (Fin n') = Fintype.card (Fin n) :=
      Fintype.card_congr (Equiv.ofBijective σ hσ)
    simpa using hcard
  subst hnn
  obtain ⟨e, he, h0, h1⟩ :=
    Work.Drive.N2C.roundToRoundIso (f := f) hf hreg L L' hD hD' σ hσ hh ε hε hcd hper hmono hrel
      (fun L₁ L₂ Dc hDc h' hcd' hper' hmono' hrel' =>
        Work.Drive.N2C.canonicalReparamIso (f := f) hf hreg L₁ L₂ Dc hDc h' hcd' hper' hmono' hrel')
      (fun c r hr => Work.Drive.N2C.shellFlip c r hr)
  exact ⟨e, he, h0, h1⟩

/-! ## The gap engine -/


/-- **The gap engine** (C1), for a compact surface. -/
theorem gapDrawing_of_certifiedEnds {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {Φ : ℝ × M → M} (hΦsm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ)
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦcomp : ∀ (s t : ℝ) (x : M), Φ (s, Φ (t, x)) = Φ (s + t, x))
    {lo0 lo h1 u1 m1 m2 u2 h2 hi hi0 : ℝ}
    (hord : lo0 < lo ∧ lo < h1 ∧ h1 < u1 ∧ u1 < m1 ∧ m1 ≤ m2 ∧ m2 < u2 ∧ u2 < h2 ∧
      h2 < hi ∧ hi < hi0)
    (hΦf : ∀ (x : M) (t : ℝ), f x ∈ Set.Icc lo0 hi0 → f x + t ∈ Set.Icc lo0 hi0 →
      f (Φ (t, x)) = f x + t)
    (hreg : ∀ x : M, f x ∈ Set.Icc lo0 hi0 → ¬ Work.Drive.Morse.IsCritical f x)
    {g1 g2 : M → EuclideanSpace ℝ (Fin 3)}
    (hg1 : Work.Drive.N2.GoodDrawingOn f (Set.Ioo lo0 m1) g1)
    (hg2 : Work.Drive.N2.GoodDrawingOn f (Set.Ioo m2 hi0) g2)
    (hc1 : IsCertifiedAt f u1 g1) (hc2 : IsCertifiedAt f u2 g2) :
    ∃ G : M → EuclideanSpace ℝ (Fin 3),
      Work.Drive.N2.GoodDrawingOn f (Set.Ioo lo hi) G ∧
      (∀ x : M, f x ∈ Set.Ioo lo h1 → G x = g1 x) ∧
      (∀ x : M, f x ∈ Set.Ioo h2 hi → G x = g2 x) := by
  classical
  obtain ⟨hl0l, hlh1, hh1u1, hu1m1, hm1m2, hm2u2, hu2h2, hh2hi, hhihi0⟩ := hord
  obtain ⟨n1, L1, D1, e1, hD1, hIso1, he10, he11⟩ := hc1
  obtain ⟨n2, L2, D2, e2, hD2, hIso2, he20, he21⟩ := hc2
  -- ## the anchor and the basic inequalities
  set b : ℝ := (m1 + m2) / 2 with hbdef
  have hbm1 : m1 ≤ b := by rw [hbdef]; linarith
  have hbm2 : b ≤ m2 := by rw [hbdef]; linarith
  have hlob : lo0 < b := by linarith
  have hbhi0 : b < hi0 := by linarith
  have hbIoo : b ∈ Set.Ioo lo0 hi0 := ⟨hlob, hbhi0⟩
  have hlo0hi0 : lo0 < hi0 := by linarith
  have hu1Ioo : u1 ∈ Set.Ioo lo0 hi0 := ⟨by linarith, by linarith⟩
  have hu2Ioo : u2 ∈ Set.Ioo lo0 hi0 := ⟨by linarith, by linarith⟩
  have hu1Icc : u1 ∈ Set.Icc lo0 hi0 := ⟨hu1Ioo.1.le, hu1Ioo.2.le⟩
  have hu2Icc : u2 ∈ Set.Icc lo0 hi0 := ⟨hu2Ioo.1.le, hu2Ioo.2.le⟩
  have hbIcc : b ∈ Set.Icc lo0 hi0 := ⟨hlob.le, hbhi0.le⟩
  have hcomp' : ∀ (x : M) (s t : ℝ), f x ∈ Set.Icc lo0 hi0 → f x + t ∈ Set.Icc lo0 hi0 →
      f x + t + s ∈ Set.Icc lo0 hi0 → Φ (s, Φ (t, x)) = Φ (s + t, x) :=
    fun x s t _ _ _ => hΦcomp s t x
  have hfootval : ∀ (u : ℝ) (y : M), f y = b → u ∈ Set.Icc lo0 hi0 → f (Φ (u - b, y)) = u := by
    intro u y hy hu
    have h1 : f y ∈ Set.Icc lo0 hi0 := by rw [hy]; exact hbIcc
    have h2 : f y + (u - b) ∈ Set.Icc lo0 hi0 := by rw [hy]; simpa using hu
    have h := hΦf y (u - b) h1 h2
    rw [hy] at h
    simpa using h
  -- ## A2, with the parametrisation exposed
  obtain ⟨L1', hL1'⟩ := levelCurves_transport_explicit (f := f) hf (a := lo0) (c := hi0)
    (b := u1) (b' := b) (by linarith) (by linarith) hlob hbhi0 hΦsm hΦ0 hΦcomp hΦf L1
  obtain ⟨L2', hL2'⟩ := levelCurves_transport_explicit (f := f) hf (a := lo0) (c := hi0)
    (b := u2) (b' := b) (by linarith) (by linarith) hlob hbhi0 hΦsm hΦ0 hΦcomp hΦf L2
  have hL1inv : ∀ (i : Fin n1) (x : ℝ), Φ (u1 - b, L1'.γ i x) = L1.γ i x := by
    intro i x
    rw [hL1' i x, hΦcomp (u1 - b) (b - u1) (L1.γ i x), show (u1 - b) + (b - u1) = 0 by ring,
      hΦ0]
  have hL2inv : ∀ (i : Fin n2) (x : ℝ), Φ (u2 - b, L2'.γ i x) = L2.γ i x := by
    intro i x
    rw [hL2' i x, hΦcomp (u2 - b) (b - u2) (L2.γ i x), show (u2 - b) + (b - u2) = 0 by ring,
      hΦ0]
  -- ## the certificate transports (B4)
  have hIsoE2 : IsLevelIsotopy f b (fun s y => e1 s (Φ (u1 - b, y))) :=
    isLevelIsotopy_transport (f := f) hf hIso1 hlo0hi0 hΦsm hΦ0 hΦf hcomp' hu1Ioo hbIoo
  have hIsoE4 : IsLevelIsotopy f b (fun s y => e2 (1 - s) (Φ (u2 - b, y))) :=
    isLevelIsotopy_transport (f := f) hf (isLevelIsotopy_rev' hIso2) hlo0hi0 hΦsm hΦ0 hΦf hcomp'
      hu2Ioo hbIoo
  -- ## the round-to-round isotopy (B7)
  have hregb : ∀ x : M, f x = b → ¬ Work.Drive.Morse.IsCritical f x := by
    intro x hx
    exact hreg x (by rw [hx]; exact hbIcc)
  obtain ⟨E3, hE3iso, hE30, hE31⟩ :=
    roundToRound_dev (f := f) hf hregb L1' L2' D1 D2 hD1 hD2
  -- ## the time constants
  set τ₂ : ℝ := (m2 + h2) / 2 with hτ₂def
  have hm2τ₂ : m2 < τ₂ := by rw [hτ₂def]; linarith
  have hτ₂h2 : τ₂ < h2 := by rw [hτ₂def]; linarith
  set L : ℝ := τ₂ - h1 with hLdef
  have hLpos : 0 < L := by rw [hLdef]; linarith
  set a1 : ℝ := h1 + L / 8 with ha1def
  set b1 : ℝ := h1 + L / 4 with hb1def
  set a2 : ℝ := h1 + 3 * L / 8 with ha2def
  set b2 : ℝ := h1 + L / 2 with hb2def
  set a3 : ℝ := h1 + 5 * L / 8 with ha3def
  set b3 : ℝ := h1 + 3 * L / 4 with hb3def
  set a4 : ℝ := h1 + 7 * L / 8 with ha4def
  set b4 : ℝ := h1 + L with hb4def
  have hb4τ₂ : b4 = τ₂ := by rw [hb4def, hLdef]; ring
  have h1a1 : h1 < a1 := by rw [ha1def]; linarith
  have ha1b1 : a1 < b1 := by rw [ha1def, hb1def]; linarith
  have hb1a2 : b1 < a2 := by rw [hb1def, ha2def]; linarith
  have ha2b2 : a2 < b2 := by rw [ha2def, hb2def]; linarith
  have hb2a3 : b2 < a3 := by rw [hb2def, ha3def]; linarith
  have ha3b3 : a3 < b3 := by rw [ha3def, hb3def]; linarith
  have hb3a4 : b3 < a4 := by rw [hb3def, ha4def]; linarith
  have ha4b4 : a4 < b4 := by rw [ha4def, hb4def]; linarith
  have hh2b4 : b4 < h2 := by rw [hb4τ₂]; exact hτ₂h2
  -- ## the clamps and the time maps
  set δ : ℝ := min ((lo - lo0) / 2) ((hi0 - hi) / 2) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (by linarith) (by linarith)
  have hδlo : lo0 < lo - δ := by
    rw [hδdef]; have := min_le_left ((lo - lo0) / 2) ((hi0 - hi) / 2); linarith
  have hδhi : hi + δ < hi0 := by
    rw [hδdef]; have := min_le_right ((lo - lo0) / 2) ((hi0 - hi) / 2); linarith
  have hloδ : lo - δ < lo := by linarith
  have hhiδ : hi < hi + δ := by linarith
  set τ₁ : ℝ := (h1 + min u1 a1) / 2 with hτ₁def
  have hτ₁h1 : h1 < τ₁ := by
    rw [hτ₁def]; have := lt_min hh1u1 h1a1; linarith
  have hτ₁u1 : τ₁ < u1 := by
    rw [hτ₁def]; have := min_le_left u1 a1; linarith
  have hτ₁a1 : τ₁ < a1 := by
    rw [hτ₁def]; have := min_le_right u1 a1; linarith
  set ρ1 : ℝ → ℝ := fun s => s + (u1 - s) * smoothStep h1 τ₁ s
    + ((lo - δ) - s) * (1 - smoothStep (lo - δ) lo s) with hρ1def
  set ρ2 : ℝ → ℝ := fun s => s + (u2 - s) * (1 - smoothStep τ₂ h2 s)
    + ((hi + δ) - s) * smoothStep hi (hi + δ) s with hρ2def
  have hρ1sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ1 := by
    rw [hρ1def]
    exact (contDiff_id.add ((contDiff_const.sub contDiff_id).mul (smoothStep_contDiff h1 τ₁))).add
      ((contDiff_const.sub contDiff_id).mul
        (contDiff_const.sub (smoothStep_contDiff (lo - δ) lo)))
  have hρ2sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ2 := by
    rw [hρ2def]
    exact (contDiff_id.add ((contDiff_const.sub contDiff_id).mul
        (contDiff_const.sub (smoothStep_contDiff τ₂ h2)))).add
      ((contDiff_const.sub contDiff_id).mul (smoothStep_contDiff hi (hi + δ)))
  -- ## the pointwise shape of the two time maps
  have hρ1self : ∀ s : ℝ, lo ≤ s → s ≤ h1 → ρ1 s = s := by
    intro s hs1 hs2
    have hgoal : ρ1 s = s + (u1 - s) * smoothStep h1 τ₁ s
        + ((lo - δ) - s) * (1 - smoothStep (lo - δ) lo s) := rfl
    rw [hgoal]
    have hb : smoothStep h1 τ₁ s = 0 := smoothStep_zero h1 τ₁ hτ₁h1 hs2
    have hc : smoothStep (lo - δ) lo s = 1 := smoothStep_one (lo - δ) lo (by linarith) hs1
    rw [hb, hc]; ring
  have hρ2self : ∀ s : ℝ, h2 ≤ s → s ≤ hi → ρ2 s = s := by
    intro s hs1 hs2
    have hgoal : ρ2 s = s + (u2 - s) * (1 - smoothStep τ₂ h2 s)
        + ((hi + δ) - s) * smoothStep hi (hi + δ) s := rfl
    rw [hgoal]
    have hb : smoothStep τ₂ h2 s = 1 := smoothStep_one τ₂ h2 hτ₂h2 (by linarith)
    have hc : smoothStep hi (hi + δ) s = 0 := smoothStep_zero hi (hi + δ) (by linarith) hs2
    rw [hb, hc]; ring
  have hρ1u1 : ∀ s : ℝ, τ₁ ≤ s → ρ1 s = u1 := by
    intro s hs
    have hgoal : ρ1 s = s + (u1 - s) * smoothStep h1 τ₁ s
        + ((lo - δ) - s) * (1 - smoothStep (lo - δ) lo s) := rfl
    rw [hgoal]
    have hb : smoothStep h1 τ₁ s = 1 := smoothStep_one h1 τ₁ hτ₁h1 hs
    have hc : smoothStep (lo - δ) lo s = 1 :=
      smoothStep_one (lo - δ) lo (by linarith) (by linarith [hs, hτ₁h1, hlh1])
    rw [hb, hc]; ring
  have hρ2u2 : ∀ s : ℝ, s ≤ τ₂ → ρ2 s = u2 := by
    intro s hs
    have hgoal : ρ2 s = s + (u2 - s) * (1 - smoothStep τ₂ h2 s)
        + ((hi + δ) - s) * smoothStep hi (hi + δ) s := rfl
    rw [hgoal]
    have hb : smoothStep τ₂ h2 s = 0 := smoothStep_zero τ₂ h2 hτ₂h2 hs
    have hc : smoothStep hi (hi + δ) s = 0 :=
      smoothStep_zero hi (hi + δ) (by linarith) (by linarith [hs, hτ₂h2, hh2hi])
    rw [hb, hc]; ring
  have hρ1mem : ∀ s : ℝ, ρ1 s ∈ Set.Icc (lo - δ) u1 := by
    intro s
    have hgoal : ρ1 s = s + (u1 - s) * smoothStep h1 τ₁ s
        + ((lo - δ) - s) * (1 - smoothStep (lo - δ) lo s) := rfl
    rw [hgoal]
    by_cases hA : s ≤ lo - δ
    · have hb : smoothStep h1 τ₁ s = 0 :=
        smoothStep_zero h1 τ₁ hτ₁h1 (by linarith [hA, hloδ, hlh1])
      have hc : smoothStep (lo - δ) lo s = 0 := smoothStep_zero (lo - δ) lo (by linarith) hA
      rw [hb, hc]
      simp only [sub_zero, mul_zero, mul_one, add_zero]
      rw [show s + ((lo - δ) - s) = lo - δ by ring]
      exact ⟨le_rfl, by linarith [hloδ, hlh1, hh1u1]⟩
    · push_neg at hA
      by_cases hB : s ≤ h1
      · have hb : smoothStep h1 τ₁ s = 0 := smoothStep_zero h1 τ₁ hτ₁h1 hB
        rw [hb]
        simp only [mul_zero, add_zero]
        have hγmem := smoothStep_mem (lo - δ) lo s
        have hγ : (1 - smoothStep (lo - δ) lo s) ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨by linarith [hγmem.2], by linarith [hγmem.1]⟩
        have hcc := convex_mem_Icc (a := s) (b := lo - δ) (γ := 1 - smoothStep (lo - δ) lo s)
          hγ.1 hγ.2
        have hconv : s + ((lo - δ) - s) * (1 - smoothStep (lo - δ) lo s)
            = (1 - (1 - smoothStep (lo - δ) lo s)) * s
              + (1 - smoothStep (lo - δ) lo s) * (lo - δ) := by ring
        rw [hconv]
        exact ⟨le_trans (le_of_eq (min_eq_right hA.le).symm) hcc.1,
          le_trans hcc.2 (by rw [max_eq_left hA.le]; exact le_of_lt (lt_of_le_of_lt hB hh1u1))⟩
      · push_neg at hB
        by_cases hC : τ₁ ≤ s
        · have hb : smoothStep h1 τ₁ s = 1 := smoothStep_one h1 τ₁ hτ₁h1 hC
          have hc : smoothStep (lo - δ) lo s = 1 :=
            smoothStep_one (lo - δ) lo (by linarith) (by linarith [hC, hτ₁h1, hlh1])
          rw [hb, hc]
          simp only [sub_self, mul_zero, add_zero, mul_one]
          rw [show s + (u1 - s) = u1 by ring]
          exact ⟨by linarith [hδlo, hloδ, hlh1, hh1u1], le_rfl⟩
        · push_neg at hC
          have hc : smoothStep (lo - δ) lo s = 1 :=
            smoothStep_one (lo - δ) lo (by linarith) (by linarith [hB, hlh1])
          rw [hc]
          simp only [sub_self, mul_zero, add_zero]
          have hβmem := smoothStep_mem h1 τ₁ s
          have hcc := convex_mem_Icc (a := s) (b := u1) (γ := smoothStep h1 τ₁ s) hβmem.1 hβmem.2
          have hconv : s + (u1 - s) * smoothStep h1 τ₁ s
              = (1 - smoothStep h1 τ₁ s) * s + smoothStep h1 τ₁ s * u1 := by ring
          rw [hconv]
          exact ⟨le_trans (le_min hA.le (by linarith [hδlo, hloδ, hlh1, hh1u1])) hcc.1,
            le_trans hcc.2 (max_le (le_of_lt (lt_trans hC hτ₁u1)) le_rfl)⟩
  have hρ2mem : ∀ s : ℝ, ρ2 s ∈ Set.Icc (min u2 τ₂) (hi + δ) := by
    intro s
    have hgoal : ρ2 s = s + (u2 - s) * (1 - smoothStep τ₂ h2 s)
        + ((hi + δ) - s) * smoothStep hi (hi + δ) s := rfl
    rw [hgoal]
    by_cases hA : s ≤ τ₂
    · have hb : smoothStep τ₂ h2 s = 0 := smoothStep_zero τ₂ h2 hτ₂h2 hA
      have hc : smoothStep hi (hi + δ) s = 0 :=
        smoothStep_zero hi (hi + δ) (by linarith) (by linarith [hA, hτ₂h2, hh2hi])
      rw [hb, hc]
      simp only [sub_zero, mul_one, mul_zero, add_zero]
      rw [show s + (u2 - s) = u2 by ring]
      exact ⟨min_le_left u2 τ₂, by linarith [hh2hi, hhihi0]⟩
    · push_neg at hA
      by_cases hB : s ≤ h2
      · have hc : smoothStep hi (hi + δ) s = 0 :=
          smoothStep_zero hi (hi + δ) (by linarith) (by linarith [hB, hh2hi])
        rw [hc]
        simp only [mul_zero, add_zero]
        have hβmem := smoothStep_mem τ₂ h2 s
        have hγ : (1 - smoothStep τ₂ h2 s) ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨by linarith [hβmem.2], by linarith [hβmem.1]⟩
        have hcc := convex_mem_Icc (a := s) (b := u2) (γ := 1 - smoothStep τ₂ h2 s) hγ.1 hγ.2
        have hconv : s + (u2 - s) * (1 - smoothStep τ₂ h2 s)
            = (1 - (1 - smoothStep τ₂ h2 s)) * s + (1 - smoothStep τ₂ h2 s) * u2 := by ring
        rw [hconv]
        exact ⟨le_trans (le_trans (le_min (min_le_left u2 τ₂) (le_trans (min_le_right u2 τ₂) hA.le))
            (le_of_eq (min_comm u2 s))) hcc.1,
          le_trans hcc.2 (max_le (by linarith [hB, hh2hi, hhihi0])
            (by linarith [hu2h2, hh2hi, hhihi0]))⟩
      · push_neg at hB
        by_cases hC : hi ≤ s
        · by_cases hD : hi + δ ≤ s
          · have hb : smoothStep τ₂ h2 s = 1 := smoothStep_one τ₂ h2 hτ₂h2 (by linarith)
            have hc : smoothStep hi (hi + δ) s = 1 := smoothStep_one hi (hi + δ) (by linarith) hD
            rw [hb, hc]
            simp only [sub_self, mul_zero, add_zero, one_mul, mul_one]
            rw [show s + (hi + δ - s) = hi + δ by ring]
            exact ⟨le_trans (min_le_left u2 τ₂) (by linarith [hu2h2, hh2hi, hhihi0]), le_rfl⟩
          · push_neg at hD
            have hb : smoothStep τ₂ h2 s = 1 := smoothStep_one τ₂ h2 hτ₂h2 (by linarith)
            rw [hb]
            simp only [sub_self, mul_zero, add_zero]
            have hεmem := smoothStep_mem hi (hi + δ) s
            have hcc := convex_mem_Icc (a := s) (b := hi + δ)
              (γ := smoothStep hi (hi + δ) s) hεmem.1 hεmem.2
            have hconv : s + (hi + δ - s) * smoothStep hi (hi + δ) s
                = (1 - smoothStep hi (hi + δ) s) * s
                  + smoothStep hi (hi + δ) s * (hi + δ) := by ring
            rw [hconv]
            exact ⟨le_trans (le_trans (min_le_right u2 τ₂) (le_of_lt (by linarith [hB, hh2hi, hτ₂h2])))
                (le_trans (le_min le_rfl (le_of_lt hD)) hcc.1),
              le_trans hcc.2 (by rw [max_eq_right hD.le])⟩
        · push_neg at hC
          have hb : smoothStep τ₂ h2 s = 1 := smoothStep_one τ₂ h2 hτ₂h2 (by linarith)
          have hc : smoothStep hi (hi + δ) s = 0 :=
            smoothStep_zero hi (hi + δ) (by linarith) hC.le
          rw [hb, hc]
          simp only [sub_self, mul_zero, add_zero, sub_zero]
          exact ⟨le_trans (min_le_right u2 τ₂) (by linarith [hB, hh2hi, hτ₂h2]),
            by linarith [hC, hh2hi, hhihi0]⟩
  -- ## the two end pieces (B5)
  have hE1 : IsLevelIsotopy f b (fun s y => g1 (Φ (ρ1 s - b, y))) :=
    isLevelIsotopy_windowMovie (f := f) hf (b := b) (W := g1) (Φ := Φ) (lo := lo0) (hi := hi0)
      (a' := lo0) (b' := m1) (α := lo - δ) (β := u1) hlo0hi0 hΦsm hΦ0 hΦf hcomp' hbIoo
      (by intro t ht; exact ⟨by linarith [ht.1, hδlo], by linarith [ht.2, hu2h2, hh2hi, hhihi0]⟩)
      (by intro t ht; exact ⟨by linarith [ht.1, hδlo], by linarith [ht.2, hu1m1]⟩)
      hg1 hρ1sm hρ1mem
  have hE5 : IsLevelIsotopy f b (fun s y => g2 (Φ (ρ2 s - b, y))) :=
    isLevelIsotopy_windowMovie (f := f) hf (b := b) (W := g2) (Φ := Φ) (lo := lo0) (hi := hi0)
      (a' := m2) (b' := hi0) (α := min u2 τ₂) (β := hi + δ) hlo0hi0 hΦsm hΦ0 hΦf hcomp' hbIoo
      (by intro t ht; exact ⟨lt_of_lt_of_le
          (lt_min hu2Ioo.1 (by linarith [hu1m1, hm1m2, hm2τ₂])) ht.1, by linarith [ht.2, hδhi]⟩)
      (by intro t ht; exact ⟨lt_of_lt_of_le (lt_min hm2u2 hm2τ₂) ht.1,
        by linarith [ht.2, hδhi]⟩)
      hg2 hρ2sm hρ2mem
  -- ## the flattened middle pieces
  have hE2 : IsLevelIsotopy f b (fun s y => e1 s (Φ (u1 - b, y))) := hIsoE2
  have hE4 : IsLevelIsotopy f b (fun s y => e2 (1 - s) (Φ (u2 - b, y))) := hIsoE4
  have hE2f : IsLevelIsotopy f b
      (fun s y => e1 (smoothStep b1 a2 s) (Φ (u1 - b, y))) :=
    isLevelIsotopy_comp_time hE2 (smoothStep_contDiff b1 a2)
  have hE3f : IsLevelIsotopy f b (fun s y => E3 (smoothStep b2 a3 s) y) :=
    isLevelIsotopy_comp_time hE3iso (smoothStep_contDiff b2 a3)
  have hE4f : IsLevelIsotopy f b
      (fun s y => e2 (1 - smoothStep b3 a4 s) (Φ (u2 - b, y))) :=
    isLevelIsotopy_comp_time hE4 (smoothStep_contDiff b3 a4)
  -- ## the four junction agreements
  have hJ12 : ∀ s ∈ Set.Icc a1 b1, ∀ y : M, f y = b →
      g1 (Φ (ρ1 s - b, y)) = e1 (smoothStep b1 a2 s) (Φ (u1 - b, y)) := by
    intro s hs y hy
    have hsτ : τ₁ ≤ s := le_of_lt (lt_of_lt_of_le hτ₁a1 hs.1)
    have hφ : smoothStep b1 a2 s = 0 := smoothStep_zero b1 a2 hb1a2 hs.2
    rw [hρ1u1 s hsτ, hφ]
    exact (he10 (Φ (u1 - b, y)) (hfootval u1 y hy hu1Icc)).symm
  have hJ23 : ∀ s ∈ Set.Icc a2 b2, ∀ y : M, f y = b →
      e1 (smoothStep b1 a2 s) (Φ (u1 - b, y)) = E3 (smoothStep b2 a3 s) y := by
    intro s hs y hy
    have hφ2 : smoothStep b1 a2 s = 1 := smoothStep_one b1 a2 hb1a2 hs.1
    have hφ3 : smoothStep b2 a3 s = 0 := smoothStep_zero b2 a3 hb2a3 hs.2
    rw [hφ2, hφ3]
    obtain ⟨i, x, hxy⟩ := L1'.cover y hy
    rw [hxy, hL1inv i x, he11 i x]
    exact (hE30 i x).symm
  have hJ34 : ∀ s ∈ Set.Icc a3 b3, ∀ y : M, f y = b →
      E3 (smoothStep b2 a3 s) y = e2 (1 - smoothStep b3 a4 s) (Φ (u2 - b, y)) := by
    intro s hs y hy
    have hφ3 : smoothStep b2 a3 s = 1 := smoothStep_one b2 a3 hb2a3 hs.1
    have hφ4 : smoothStep b3 a4 s = 0 := smoothStep_zero b3 a4 hb3a4 hs.2
    rw [hφ3, hφ4, sub_zero]
    obtain ⟨i, x, hxy⟩ := L2'.cover y hy
    rw [hxy, hL2inv i x, he21 i x]
    exact hE31 i x
  have hJ45 : ∀ s ∈ Set.Icc a4 b4, ∀ y : M, f y = b →
      e2 (1 - smoothStep b3 a4 s) (Φ (u2 - b, y)) = g2 (Φ (ρ2 s - b, y)) := by
    intro s hs y hy
    have hφ4 : smoothStep b3 a4 s = 1 := smoothStep_one b3 a4 hb3a4 hs.1
    have hsτ : s ≤ τ₂ := le_trans hs.2 hb4τ₂.le
    rw [hφ4, sub_self, hρ2u2 s hsτ]
    exact he20 (Φ (u2 - b, y)) (hfootval u2 y hy hu2Icc)
  -- ## the concatenation (B3)
  have hJ12' : ∀ s ∈ Set.Icc a1 b1, ∀ y : M, f y = b →
      (fun s y => g1 (Φ (ρ1 s - b, y))) s y
        = (fun s y => e1 (smoothStep b1 a2 s) (Φ (u1 - b, y))) s y := hJ12
  obtain ⟨G1, hG1iso, hG1l, hG1r⟩ :=
    isLevelIsotopy_blend (f := f) hf hregb hE1 hE2f ha1b1 hJ12'
  have hJ23' : ∀ s ∈ Set.Icc a2 b2, ∀ y : M, f y = b → G1 s y
      = (fun s y => E3 (smoothStep b2 a3 s) y) s y := by
    intro s hs y hy
    rw [hG1r s (le_trans hb1a2.le hs.1)]
    exact hJ23 s hs y hy
  obtain ⟨G2, hG2iso, hG2l, hG2r⟩ :=
    isLevelIsotopy_blend (f := f) hf hregb hG1iso hE3f ha2b2 hJ23'
  have hJ34' : ∀ s ∈ Set.Icc a3 b3, ∀ y : M, f y = b → G2 s y
      = (fun s y => e2 (1 - smoothStep b3 a4 s) (Φ (u2 - b, y))) s y := by
    intro s hs y hy
    rw [hG2r s (le_trans hb2a3.le hs.1)]
    exact hJ34 s hs y hy
  obtain ⟨G3, hG3iso, hG3l, hG3r⟩ :=
    isLevelIsotopy_blend (f := f) hf hregb hG2iso hE4f ha3b3 hJ34'
  have hJ45' : ∀ s ∈ Set.Icc a4 b4, ∀ y : M, f y = b → G3 s y
      = (fun s y => g2 (Φ (ρ2 s - b, y))) s y := by
    intro s hs y hy
    rw [hG3r s (le_trans hb3a4.le hs.1)]
    exact hJ45 s hs y hy
  obtain ⟨e, heIso, hel, her⟩ :=
    isLevelIsotopy_blend (f := f) hf hregb hG3iso hE5 ha4b4 hJ45'
  -- ## the drawing
  have hfootb : ∀ z : M, f z ∈ Set.Icc lo hi → f (Φ (b - f z, z)) = b := by
    intro z hz
    have h2 : f z + (b - f z) ∈ Set.Icc lo0 hi0 := by
      rw [show f z + (b - f z) = b by ring]; exact hbIcc
    have h := hΦf z (b - f z) ⟨by linarith [hz.1, hl0l, hδlo], by linarith [hz.2, hhihi0, hδhi]⟩ h2
    rwa [show f z + (b - f z) = b by ring] at h
  have hfootRow : ∀ z : M, f z ∈ Set.Icc lo hi → ∀ s : ℝ,
      ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M => e p.1 p.2) (s, Φ (b - f z, z)) :=
    fun z hz s => heIso.1 s _ (hfootb z hz)
  refine ⟨fun z => e (f z) (Φ (b - f z, z)), ?_, ?_, ?_⟩
  · exact Work.Drive.N2.collarDrawing_wide (f := f) hf (lo := lo) (b := b) (hi := hi)
      (by linarith) (by linarith) hΦsm hΦ0
      (fun x t h1 h2 => hΦf x t ⟨by linarith [h1.1, hl0l, hδlo], by linarith [h1.2, hhihi0, hδhi]⟩
        ⟨by linarith [h2.1, hl0l, hδlo], by linarith [h2.2, hhihi0, hδhi]⟩)
      (fun x s t h1 h2 h3 => hΦcomp s t x) e hfootRow heIso.2.1 heIso.2.2 (fun s => s)
      (by fun_prop)
  · intro x hx
    have hxa1 : f x ≤ a1 := le_of_lt (lt_of_lt_of_le hx.2 h1a1.le)
    have hchain : e (f x) = (fun s y => g1 (Φ (ρ1 s - b, y))) (f x) := by
      rw [hel (f x) (by linarith), hG3l (f x) (by linarith), hG2l (f x) (by linarith),
        hG1l (f x) hxa1]
    show e (f x) (Φ (b - f x, x)) = g1 x
    rw [hchain]
    show g1 (Φ (ρ1 (f x) - b, Φ (b - f x, x))) = g1 x
    have hΦx : Φ (ρ1 (f x) - b, Φ (b - f x, x)) = Φ (ρ1 (f x) - f x, x) := by
      rw [hΦcomp (ρ1 (f x) - b) (b - f x) x]
      congr 1
      ring
    rw [hΦx]
    have hρx : ρ1 (f x) = f x := hρ1self (f x) hx.1.le hx.2.le
    rw [hρx, show f x - f x = (0 : ℝ) by ring, hΦ0]
  · intro x hx
    have hxb4 : b4 ≤ f x := le_of_lt (lt_trans hh2b4 hx.1)
    have hchain : e (f x) = (fun s y => g2 (Φ (ρ2 s - b, y))) (f x) := her (f x) hxb4
    show e (f x) (Φ (b - f x, x)) = g2 x
    rw [hchain]
    show g2 (Φ (ρ2 (f x) - b, Φ (b - f x, x))) = g2 x
    have hΦx : Φ (ρ2 (f x) - b, Φ (b - f x, x)) = Φ (ρ2 (f x) - f x, x) := by
      rw [hΦcomp (ρ2 (f x) - b) (b - f x) x]
      congr 1
      ring
    rw [hΦx]
    have hρx : ρ2 (f x) = f x := hρ2self (f x) hx.1.le hx.2.le
    rw [hρx, show f x - f x = (0 : ℝ) by ring, hΦ0]


/-- **The placement isotopy** (one of the two ingredients of the Tier B round-to-round isotopy): two
disjoint round configurations read through the *same* parametrisation of a regular level are joined by
a level isotopy.  `Work.Drive.N2.roundConfigPath` supplies the path of configurations and
`Work.Drive.N2.roundConfigPictureGlobal` the jointly smooth picture family. -/
theorem roundToRound_sameParam [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) {b : ℝ}
    (hreg : ∀ x : M, f x = b → ¬ Work.Drive.Morse.IsCritical f x)
    {n : ℕ} (L : LevelCurves f b n) {D D' : Work.Drive.N2.RoundConfig n}
    (hD : D.Disjoint) (hD' : D'.Disjoint) :
    ∃ e : ℝ → M → EuclideanSpace ℝ (Fin 3), IsLevelIsotopy f b e ∧
      (∀ (i : Fin n) (x : ℝ), e 0 (L.γ i x) = D.circle i x) ∧
      (∀ (i : Fin n) (x : ℝ), e 1 (L.γ i x) = D'.circle i x) := by
  obtain ⟨Dp, hDp0, hDp1, -, -, hDpd, hDppos, hDprad, hDpph⟩ :=
    Work.Drive.N2.roundConfigPath D D' hD hD'
  obtain ⟨P, hPc, hPinj, hPimm, hPsm⟩ :=
    Work.Drive.N2.roundConfigPictureGlobal (f := f) (b := b) (n := n) L.γ hf hreg L.sm L.val
      L.per L.injIco L.cover L.disj L.ker hDpd hDppos hDprad hDpph
  refine ⟨P, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro s y _
    exact hPsm.contMDiffAt
  · intro s x y hx hy hxy
    obtain ⟨i, t, rfl⟩ := L.cover x hx
    obtain ⟨j, u, rfl⟩ := L.cover y hy
    exact hPinj s _ _ ⟨i, t, rfl⟩ ⟨j, u, rfl⟩ hxy
  · intro s y hy v hv hv'
    obtain ⟨i, t, rfl⟩ := L.cover y hy
    exact hPimm s _ ⟨i, t, rfl⟩ v hv hv'
  · intro i x
    rw [hPc 0 i x, hDp0]
  · intro i x
    rw [hPc 1 i x, hDp1]

end Work.Drive.N2C.H7
