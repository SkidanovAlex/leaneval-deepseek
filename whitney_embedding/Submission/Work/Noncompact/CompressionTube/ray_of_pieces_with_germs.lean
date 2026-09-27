import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.germGlue
import Submission.Work.Noncompact.CompressionTube.immersedArcWithGerm

/-!
# Assembling a ray out of germ-matched pieces

`Work.Noncompact.CompressionTube.ray_of_pieces_with_germs`: an `ℕ`-indexed family of pieces
`P i : ℝ → M`, each `C^∞`, an immersion and injective on `[0,1]`, with `P i 1 = P (i+1) 0` and
with *matching germs* at the junctions (both pieces agree, near the junction, with the same
straight chart line), pairwise separated (`P i '' Icc ∩ P j '' Icc ⊆ {P i 1}` for `i < j`) and
escaping every compact set, assembles into a ray `r : ℝ → M` which

* equals the straight chart germ on `(-∞,e]` (so it is `C^∞` and an immersion at `0`, where the
  piece family alone says nothing),
* is `C^∞` and an immersion on `[0,∞)`,
* is injective on `[0,∞)`,
* is proper on `[0,∞)`,
* takes its values on `[0,∞)` inside `{P 0 0} ∪ ⋃ i, P i '' Icc 0 1`.

The assembled ray is `r t = P ⌊t⌋₊ (t - ⌊t⌋₊)` for `t > 0`, and the straight chart germ for
`t ≤ 0`.
-/

namespace Work.Noncompact.CompressionTube

open Set Topology Function
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (MC n) smoothOrder M] [T2Space M] [SecondCountableTopology M]

/-- A straight chart germ is a smooth immersion near its base point. -/
private lemma chartLine_data {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M) {p : M} (hp : p ∈ c.source)
    {w : EuclideanSpace ℝ (Fin n)} (hw : w ≠ 0) :
    ∃ T : Set ℝ, IsOpen T ∧ (0:ℝ) ∈ T ∧
      ContMDiffOn MCreal (MC n) smoothOrder (fun t : ℝ => c.symm (c p + t • w)) T ∧
      Function.Injective (mfderiv MCreal (MC n) (fun t : ℝ => c.symm (c p + t • w)) 0) := by
  obtain ⟨ρ, hρ0, hρ⟩ := Metric.isOpen_iff.mp c.open_target (c p) (c.map_source hp)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hqpos : 0 < ρ / (2 * ‖w‖) := by positivity
  have hmem : ∀ v : ℝ, |v| < ρ / (2 * ‖w‖) → c p + v • w ∈ c.target := by
    intro v hv
    apply hρ
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have h2 : ρ / (2 * ‖w‖) * (2 * ‖w‖) = ρ := div_mul_cancel₀ ρ (by positivity)
    nlinarith [hv, h2, hwpos]
  have h := isImmersion_chartLine (n := n) c hc hp hw
    (T := Set.Ioo (-(ρ / (2 * ‖w‖))) (ρ / (2 * ‖w‖))) isOpen_Ioo
    (fun v hv => hmem v (by rw [abs_lt]; exact hv))
  exact ⟨_, isOpen_Ioo, ⟨by linarith [hqpos], hqpos⟩, h.1, h.2 0 ⟨by linarith [hqpos], hqpos⟩⟩

/-- The reparametrisation transfer for the derivative. -/
private lemma reparam_transfer {f : ℝ → M} {a : ℝ → ℝ} {x : ℝ}
    (hfd : MDifferentiableAt MCreal (MC n) f (a x)) (had : MDifferentiableAt MCreal MCreal a x)
    (hac : Function.Injective (mfderiv MCreal MCreal a x))
    (hf : Function.Injective (mfderiv MCreal (MC n) f (a x))) :
    Function.Injective (mfderiv MCreal (MC n) (fun s : ℝ => f (a s)) x) := by
  have hL : mfderiv MCreal (MC n) (fun s : ℝ => f (a s)) x
      = (mfderiv MCreal (MC n) f (a x)).comp (mfderiv MCreal MCreal a x) := by
    rw [show (fun s : ℝ => f (a s)) = f ∘ a from rfl, mfderiv_comp x hfd had]
  rw [hL, ContinuousLinearMap.coe_comp]
  exact Function.Injective.comp hf hac

theorem ray_of_pieces_with_germs {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M] [T2Space M]
    [SecondCountableTopology M]
    (P : ℕ → ℝ → M)
    (hsm : ∀ i : ℕ, ContMDiff MCreal (MC n) smoothOrder (P i))
    (himm : ∀ (i : ℕ) (t : ℝ), t ∈ Set.Icc (0:ℝ) 1 →
      Function.Injective (mfderiv MCreal (MC n) (P i) t))
    (hinj : ∀ i : ℕ, Set.InjOn (P i) (Set.Icc (0:ℝ) 1))
    (hjun : ∀ i : ℕ, P i 1 = P (i + 1) 0)
    (hgerm : ∀ i : ℕ, ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (u : EuclideanSpace ℝ (Fin n)) (e' : ℝ),
        0 < e' ∧ c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M ∧ P i 1 ∈ c.source ∧
        (∀ t : ℝ, 1 - e' ≤ t → t ≤ 1 → P i t = c.symm (c (P i 1) + (t - 1) • u)) ∧
        (∀ t : ℝ, 0 ≤ t → t ≤ e' → P (i + 1) t = c.symm (c (P (i + 1) 0) + t • u)))
    (hsep : ∀ i j : ℕ, i < j → P i '' Set.Icc (0:ℝ) 1 ∩ P j '' Set.Icc (0:ℝ) 1 ⊆ {P i 1})
    (hesc : ∀ K : Set M, IsCompact K → ∃ I : ℕ, ∀ i : ℕ, I ≤ i → P i '' Set.Icc (0:ℝ) 1 ∩ K = ∅)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n)}
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hu0 : u ≠ 0)
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M) (hu : P 0 0 ∈ c.source)
    (hgerm0 : ∀ t : ℝ, 0 ≤ t → t ≤ e → P 0 t = c.symm (c (P 0 0) + t • u)) :
    ∃ r : ℝ → M, (∀ t : ℝ, t ≤ 0 → r t = c.symm (c (P 0 0) + t • u)) ∧
      ContMDiffOn MCreal (MC n) smoothOrder r (Set.Ici 0) ∧
      Set.InjOn r (Set.Ici (0:ℝ)) ∧
      IsProperMap (fun t : Set.Ici (0:ℝ) => r t) ∧
      (∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv MCreal (MC n) r t)) ∧
      (∀ t : ℝ, 0 ≤ t → r t ∈ ({P 0 0} ∪ ⋃ i : ℕ, P i '' Set.Icc (0:ℝ) 1)) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → r t = c.symm (c (P 0 0) + t • u)) := by
  classical
  set r : ℝ → M := fun t => if t ≤ 0 then c.symm (c (P 0 0) + t • u) else P ⌊t⌋₊ (t - ⌊t⌋₊)
    with hr
  have hr_le : ∀ {t : ℝ}, t ≤ 0 → r t = c.symm (c (P 0 0) + t • u) := by
    intro t ht; rw [hr]; exact if_pos ht
  have hr_pos : ∀ {t : ℝ}, 0 < t → r t = P ⌊t⌋₊ (t - ⌊t⌋₊) := by
    intro t ht; rw [hr]; exact if_neg (not_le.mpr ht)
  have hfloor_mem : ∀ {t : ℝ}, 0 ≤ t → t - (⌊t⌋₊ : ℝ) ∈ Set.Icc (0:ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [Nat.floor_le ht], by linarith [Nat.lt_floor_add_one t]⟩
  have hr_zero : r 0 = P 0 0 := by
    rw [hr_le le_rfl, zero_smul, add_zero]
    exact c.left_inv hu
  have hr_nonneg : ∀ {t : ℝ}, 0 ≤ t → r t = P ⌊t⌋₊ (t - ⌊t⌋₊) := by
    intro t ht
    rcases eq_or_lt_of_le ht with h | h
    · subst h; rw [hr_zero]; norm_num
    · exact hr_pos h
  -- ## `r` agrees with the chart germ below `e`
  have hr_germ_le : ∀ {t : ℝ}, t ≤ e → r t = c.symm (c (P 0 0) + t • u) := by
    intro t ht
    rcases le_or_gt t 0 with h | h
    · exact hr_le h
    · rcases lt_or_eq_of_le (le_trans ht he1) with hlt | heq
      · rw [hr_pos h]
        have hf : ⌊t⌋₊ = 0 := Nat.floor_eq_on_Ico 0 t
          ⟨by simp only [Nat.cast_zero]; exact le_of_lt h, by simpa using hlt⟩
        rw [hf]
        simpa using hgerm0 t (le_of_lt h) ht
      · subst heq
        rw [hr_pos (by norm_num : (0:ℝ) < 1)]
        have hf : ⌊(1:ℝ)⌋₊ = 1 := Nat.floor_one
        rw [hf]
        norm_num only [Nat.cast_one, sub_self]
        rw [← hjun 0]
        exact hgerm0 1 (by norm_num) (by linarith)
  -- ## the straight germ at the base point
  obtain ⟨T₀, hT₀open, hT₀mem, hT₀sm, hT₀imm⟩ := chartLine_data (n := n) hc hu hu0
  have hline_sm : ContMDiffAt MCreal (MC n) smoothOrder
      (fun t : ℝ => c.symm (c (P 0 0) + t • u)) 0 := hT₀sm.contMDiffAt (hT₀open.mem_nhds hT₀mem)
  -- ## the junction facts: for every integer junction `k ≥ 1` the ray is smooth there, is the
  -- shifted straight chart line there, and is the glue of the two pieces there
  have hjunc : ∀ k : ℕ, 1 ≤ k →
      ∃ (c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (u' : EuclideanSpace ℝ (Fin n)),
        c' ∈ IsManifold.maximalAtlas (MC n) smoothOrder M ∧ P k 0 ∈ c'.source ∧ u' ≠ 0 ∧
        ContMDiffAt MCreal (MC n) smoothOrder r (k:ℝ) ∧
        (r =ᶠ[𝓝 ((k:ℝ))] (fun s : ℝ => c'.symm (c' (P k 0) + (s - (k:ℝ)) • u'))) := by
    intro k hk1
    obtain ⟨c', u', e', he'pos, hc', hp_src, hg1, hg2⟩ := hgerm (k - 1)
    have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk1
    have hcast : ((k - 1 : ℕ) : ℝ) = (k:ℝ) - 1 := by rw [Nat.cast_sub hk1]; norm_num
    have hp_eq : P k 0 = P (k - 1) 1 := by rw [← hk']; exact (hjun (k - 1)).symm
    have hp_src' : P k 0 ∈ c'.source := by rw [hp_eq]; exact hp_src
    have hAgerm : ∀ s : ℝ, (k:ℝ) - e' ≤ s → s ≤ (k:ℝ) →
        P (k - 1) (s - ((k - 1 : ℕ) : ℝ))
          = c'.symm (c' (P k 0) + (s - (k:ℝ)) • u') := by
      intro s hs1 hs2
      have h1 : 1 - e' ≤ s - ((k - 1 : ℕ) : ℝ) := by rw [hcast]; linarith
      have h2 : s - ((k - 1 : ℕ) : ℝ) ≤ 1 := by rw [hcast]; linarith
      rw [hg1 (s - ((k - 1 : ℕ) : ℝ)) h1 h2, ← hp_eq]
      congr 2
      rw [hcast]; ring
    have hBgerm : ∀ s : ℝ, (k:ℝ) ≤ s → s ≤ (k:ℝ) + e' →
        P k (s - (k:ℝ)) = c'.symm (c' (P k 0) + (s - (k:ℝ)) • u') := by
      intro s hs1 hs2
      have h := hg2 (s - (k:ℝ)) (by linarith) (by linarith)
      rwa [hk'] at h
    have hu'0 : u' ≠ 0 := by
      intro h0
      have h0e : (0:ℝ) < min e' 1 / 2 := by positivity
      have hle : min e' 1 / 2 ≤ e' := by linarith [min_le_left e' 1]
      have hle1 : min e' 1 / 2 ≤ 1 := by linarith [min_le_right e' 1]
      have hsc : P k (min e' 1 / 2) = P k 0 := by
        have h1 : (k:ℝ) ≤ (k:ℝ) + min e' 1 / 2 := by linarith
        have h2 : (k:ℝ) + min e' 1 / 2 ≤ (k:ℝ) + e' := by linarith
        have hh := hBgerm ((k:ℝ) + min e' 1 / 2) h1 h2
        rw [show (k:ℝ) + min e' 1 / 2 - (k:ℝ) = min e' 1 / 2 from by ring] at hh
        rw [hh, h0, smul_zero, add_zero]
        exact c'.left_inv hp_src'
      have hcon := hinj k ⟨le_of_lt h0e, hle1⟩ ⟨le_rfl, zero_le_one⟩ hsc
      linarith
    have hglue := contMDiffAt_glue_same_germ (n := n) (c := c') hc' hp_src' (w := u')
      (A := fun s : ℝ => P (k - 1) (s - ((k - 1 : ℕ) : ℝ)))
      (B := fun s : ℝ => P k (s - (k:ℝ))) (τ := (k:ℝ)) (δ := e') he'pos hAgerm hBgerm
    have hLk : max ((k:ℝ) - 1) ((k:ℝ) - e') < (k:ℝ) := max_lt (by linarith) (by linarith)
    have hkU : (k:ℝ) < min ((k:ℝ) + 1) ((k:ℝ) + e') := lt_min (by linarith) (by linarith)
    have hN : Set.Ioo (max ((k:ℝ) - 1) ((k:ℝ) - e')) (min ((k:ℝ) + 1) ((k:ℝ) + e'))
        ∈ 𝓝 ((k:ℝ)) := isOpen_Ioo.mem_nhds ⟨hLk, hkU⟩
    have hk1' : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
    have hfl_lt : ∀ s : ℝ, max ((k:ℝ) - 1) ((k:ℝ) - e') < s → s < (k:ℝ) → ⌊s⌋₊ = k - 1 := by
      intro s hs1 _
      refine Nat.floor_eq_on_Ico (k - 1) s ⟨?_, ?_⟩
      · rw [hcast]; linarith [le_of_lt hs1, le_max_left ((k:ℝ) - 1) ((k:ℝ) - e')]
      · rw [hcast]; linarith
    have hfl_ge : ∀ s : ℝ, s < min ((k:ℝ) + 1) ((k:ℝ) + e') → (k:ℝ) ≤ s → ⌊s⌋₊ = k := by
      intro s hs2 hge
      exact Nat.floor_eq_on_Ico k s
        ⟨hge, by linarith [lt_of_lt_of_le hs2 (min_le_left ((k:ℝ) + 1) ((k:ℝ) + e'))]⟩
    have hgpos : ∀ s : ℝ, max ((k:ℝ) - 1) ((k:ℝ) - e') < s → 0 < s := by
      intro s hs1
      linarith [le_of_lt hs1, hk1', le_max_left ((k:ℝ) - 1) ((k:ℝ) - e')]
    have hline_ev : r =ᶠ[𝓝 ((k:ℝ))]
        (fun s : ℝ => c'.symm (c' (P k 0) + (s - (k:ℝ)) • u')) := by
      filter_upwards [hN] with s hs
      by_cases hsle : s ≤ (k:ℝ)
      · rcases lt_or_eq_of_le hsle with hlt | heq
        · rw [hr_pos (hgpos s hs.1), hfl_lt s hs.1 hlt]
          exact hAgerm s (le_of_lt (lt_of_le_of_lt (le_max_right ((k:ℝ) - 1) ((k:ℝ) - e')) hs.1)) hsle
        · subst heq
          rw [hr_nonneg (Nat.cast_nonneg k), Nat.floor_natCast]
          simp only [sub_self, zero_smul, add_zero]
          exact (c'.left_inv hp_src').symm
      · have hge : (k:ℝ) ≤ s := le_of_lt (not_le.mp hsle)
        rw [hr_pos (by linarith [hge, (Nat.cast_nonneg k : (0:ℝ) ≤ (k:ℝ))]), hfl_ge s hs.2 hge]
        exact hBgerm s hge (le_of_lt (lt_of_lt_of_le hs.2 (min_le_right ((k:ℝ) + 1) ((k:ℝ) + e'))))
    have hglue_ev : r =ᶠ[𝓝 ((k:ℝ))]
        (fun s : ℝ => if s ≤ (k:ℝ) then P (k - 1) (s - ((k - 1 : ℕ) : ℝ))
          else P k (s - (k:ℝ))) := by
      filter_upwards [hN] with s hs
      by_cases hsle : s ≤ (k:ℝ)
      · rw [if_pos hsle]
        rcases lt_or_eq_of_le hsle with hlt | heq
        · rw [hr_pos (hgpos s hs.1), hfl_lt s hs.1 hlt]
        · subst heq
          rw [hr_nonneg (Nat.cast_nonneg k), Nat.floor_natCast]
          rw [show (k:ℝ) - (k:ℝ) = 0 from by ring, hp_eq]
          congr 1
          rw [hcast]; ring
      · rw [if_neg hsle]
        have hge : (k:ℝ) ≤ s := le_of_lt (not_le.mp hsle)
        rw [hr_pos (by linarith [hge, (Nat.cast_nonneg k : (0:ℝ) ≤ (k:ℝ))]), hfl_ge s hs.2 hge]
    exact ⟨c', u', hc', hp_src', hu'0, hglue.congr_of_eventuallyEq hglue_ev, hline_ev⟩
  -- ## smoothness at a positive parameter
  have hsl : ∀ t : ℝ, 0 < t → ContMDiffAt MCreal (MC n) smoothOrder r t := by
    intro t ht
    set k : ℕ := ⌊t⌋₊ with hk
    have hk_le : (k:ℝ) ≤ t := Nat.floor_le (le_of_lt ht)
    have hk_lt : t < (k:ℝ) + 1 := by simpa using Nat.lt_floor_add_one t
    rcases eq_or_lt_of_le (by linarith : (0:ℝ) ≤ t - (k:ℝ)) with h0 | h0
    · have htk : t = (k:ℝ) := by linarith
      have hk1 : 1 ≤ k := by
        have hpos : (0:ℝ) < (k:ℝ) := by rw [← htk]; exact ht
        exact_mod_cast hpos
      obtain ⟨c', u', _, _, _, hsmk, _⟩ := hjunc k hk1
      rwa [htk]
    · have hmem : Set.Ioo (k:ℝ) ((k:ℝ) + 1) ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨by linarith, hk_lt⟩
      have hev : r =ᶠ[𝓝 t] (fun s : ℝ => P k (s - (k:ℝ))) := by
        filter_upwards [hmem] with s hs
        rw [hr_pos (by linarith [hs.1, (Nat.cast_nonneg k : (0:ℝ) ≤ (k:ℝ))])]
        have hfl : ⌊s⌋₊ = k := Nat.floor_eq_on_Ico k s ⟨le_of_lt hs.1, by simpa using hs.2⟩
        rw [hfl]
      have hperm : ContMDiffAt MCreal MCreal smoothOrder (fun s : ℝ => s - (k:ℝ)) t :=
        contMDiffAt_id.sub contMDiffAt_const
      exact ((hsm k).contMDiffAt.comp t hperm).congr_of_eventuallyEq hev
  -- ## smoothness on `[0,∞)`
  have hsmr : ContMDiffOn MCreal (MC n) smoothOrder r (Set.Ici 0) := by
    intro t ht
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ t from ht) with h | h
    · subst h
      refine (hline_sm.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [isOpen_Ioo.mem_nhds (show (0:ℝ) ∈ Set.Ioo (-e) e from ⟨by linarith, he⟩)]
        with s hs
      exact hr_germ_le hs.2.le
    · exact (hsl t h).contMDiffWithinAt
  -- ## injectivity
  have hinj_r : Set.InjOn r (Set.Ici (0:ℝ)) := by
    intro s hs t ht hst
    have hs0 : (0:ℝ) ≤ s := hs
    have ht0 : (0:ℝ) ≤ t := ht
    set ms : ℕ := ⌊s⌋₊ with hms
    set mt : ℕ := ⌊t⌋₊ with hmt
    have hsval : r s = P ms (s - (ms:ℝ)) := hr_nonneg hs0
    have htval : r t = P mt (t - (mt:ℝ)) := hr_nonneg ht0
    have hsmem : s - (ms:ℝ) ∈ Set.Icc (0:ℝ) 1 := hfloor_mem hs0
    have htmem : t - (mt:ℝ) ∈ Set.Icc (0:ℝ) 1 := hfloor_mem ht0
    have hkey : P ms (s - (ms:ℝ)) = P mt (t - (mt:ℝ)) := by rw [← hsval, ← htval]; exact hst
    rcases lt_trichotomy ms mt with hlt | heq | hgt
    · have hmem1 : P ms (s - (ms:ℝ)) ∈ P ms '' Set.Icc (0:ℝ) 1 := ⟨_, hsmem, rfl⟩
      have hmem2 : P ms (s - (ms:ℝ)) ∈ P mt '' Set.Icc (0:ℝ) 1 := ⟨_, htmem, hkey.symm⟩
      have h1 : P ms (s - (ms:ℝ)) = P ms 1 := by
        simpa using hsep ms mt hlt ⟨hmem1, hmem2⟩
      have hs_one : s = (ms:ℝ) + 1 := by
        have := hinj ms hsmem (by norm_num) h1
        linarith
      have hpt_eq : P (ms + 1) 0 = P mt (t - (mt:ℝ)) := by
        rw [← hjun ms, ← h1, hkey]
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with heq2 | hlt2
      · have hmt0 : P mt (t - (mt:ℝ)) = P mt 0 := by
          rw [hpt_eq.symm]
          exact congrArg (fun i : ℕ => P i 0) heq2
        have ht_eq : t = (mt:ℝ) := by
          have := hinj mt htmem (by norm_num) hmt0
          linarith
        have hsum : (ms:ℝ) + 1 = (mt:ℝ) := by rw [← heq2]; push_cast; ring
        rw [hs_one, hsum, ht_eq]
      · have hmem3 : P mt (t - (mt:ℝ)) ∈ P (ms + 1) '' Set.Icc (0:ℝ) 1 :=
          ⟨0, ⟨le_rfl, zero_le_one⟩, hpt_eq⟩
        have hmem4 : P mt (t - (mt:ℝ)) ∈ P mt '' Set.Icc (0:ℝ) 1 := ⟨_, htmem, rfl⟩
        have h2 : P (ms + 1) 0 = P (ms + 1) 1 :=
          hpt_eq.trans (by simpa using hsep (ms + 1) mt hlt2 ⟨hmem3, hmem4⟩)
        have : (0:ℝ) = 1 := hinj (ms + 1) (by norm_num) (by norm_num) h2
        norm_num at this
    · have hcast_eq : (ms:ℝ) = (mt:ℝ) := by rw [heq]
      have hmm : P mt (s - (mt:ℝ)) = P mt (t - (mt:ℝ)) := by rw [heq] at hkey; exact hkey
      have hsmm : s - (mt:ℝ) ∈ Set.Icc (0:ℝ) 1 := by rw [heq] at hsmem; exact hsmem
      have hsub : s - (mt:ℝ) = t - (mt:ℝ) := hinj mt hsmm htmem hmm
      linarith
    · have hmem1 : P mt (t - (mt:ℝ)) ∈ P mt '' Set.Icc (0:ℝ) 1 := ⟨_, htmem, rfl⟩
      have hmem2 : P mt (t - (mt:ℝ)) ∈ P ms '' Set.Icc (0:ℝ) 1 := ⟨_, hsmem, hkey⟩
      have h1 : P mt (t - (mt:ℝ)) = P mt 1 := by
        simpa using hsep mt ms hgt ⟨hmem1, hmem2⟩
      have ht_one : t = (mt:ℝ) + 1 := by
        have := hinj mt htmem (by norm_num) h1
        linarith
      have hpt_eq : P (mt + 1) 0 = P ms (s - (ms:ℝ)) := by
        rw [← hjun mt, ← h1, hkey.symm]
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hgt) with heq2 | hlt2
      · have hms0 : P ms (s - (ms:ℝ)) = P ms 0 := by
          rw [hpt_eq.symm]
          exact congrArg (fun i : ℕ => P i 0) heq2
        have hs_eq : s = (ms:ℝ) := by
          have := hinj ms hsmem (by norm_num) hms0
          linarith
        have hsum : (mt:ℝ) + 1 = (ms:ℝ) := by rw [← heq2]; push_cast; ring
        rw [ht_one, hsum, hs_eq]
      · have hmem3 : P ms (s - (ms:ℝ)) ∈ P (mt + 1) '' Set.Icc (0:ℝ) 1 :=
          ⟨0, ⟨le_rfl, zero_le_one⟩, hpt_eq⟩
        have hmem4 : P ms (s - (ms:ℝ)) ∈ P ms '' Set.Icc (0:ℝ) 1 := ⟨_, hsmem, rfl⟩
        have h2 : P (mt + 1) 0 = P (mt + 1) 1 :=
          hpt_eq.trans (by simpa using hsep (mt + 1) ms hlt2 ⟨hmem3, hmem4⟩)
        have : (0:ℝ) = 1 := hinj (mt + 1) (by norm_num) (by norm_num) h2
        norm_num at this
  -- ## properness
  have hcont : Continuous (fun t : Set.Ici (0:ℝ) => r t) :=
    continuousOn_iff_continuous_domRestrict.mp hsmr.continuousOn
  have hprop : IsProperMap (fun t : Set.Ici (0:ℝ) => r t) := by
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨hcont, ?_⟩
    intro K hK
    obtain ⟨I, hI⟩ := hesc K hK
    have hgcont : Continuous (fun x : ℝ =>
        (⟨max x 0, le_max_right x 0⟩ : Set.Ici (0:ℝ))) :=
      Continuous.subtype_mk (continuous_id.max continuous_const) _
    refine IsCompact.of_isClosed_subset
      ((isCompact_Icc (a := (0:ℝ)) (b := ((I:ℝ) + 1))).image hgcont)
      (hK.isClosed.preimage hcont) ?_
    intro t ht
    refine ⟨(t:ℝ), ⟨t.2, ?_⟩, ?_⟩
    · by_contra hcon
      push_neg at hcon
      have hle : I ≤ ⌊(t:ℝ)⌋₊ := Nat.le_floor (by linarith [hcon] : (I:ℝ) ≤ (t:ℝ))
      have hmem : r (t:ℝ) ∈ P ⌊(t:ℝ)⌋₊ '' Set.Icc (0:ℝ) 1 :=
        ⟨(t:ℝ) - ⌊(t:ℝ)⌋₊, hfloor_mem t.2, (hr_nonneg t.2).symm⟩
      have hdisj : Disjoint (P ⌊(t:ℝ)⌋₊ '' Set.Icc (0:ℝ) 1) K :=
        Set.disjoint_iff_inter_eq_empty.mpr (hI ⌊(t:ℝ)⌋₊ hle)
      exact (Set.disjoint_left.mp hdisj hmem) ht
    · exact Subtype.ext (by simp [max_eq_left (show (0:ℝ) ≤ (t:ℝ) from t.2)])
  -- ## immersion
  have himmr : ∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv MCreal (MC n) r t) := by
    intro t ht
    rcases eq_or_lt_of_le ht with h | h
    · subst h
      have hev : r =ᶠ[𝓝 (0:ℝ)] (fun s : ℝ => c.symm (c (P 0 0) + s • u)) := by
        filter_upwards [isOpen_Ioo.mem_nhds (show (0:ℝ) ∈ Set.Ioo (-e) e from ⟨by linarith, he⟩)]
          with s hs
        exact hr_germ_le hs.2.le
      rw [hev.mfderiv_eq]
      exact hT₀imm
    · set k : ℕ := ⌊t⌋₊ with hk
      have hk_le : (k:ℝ) ≤ t := Nat.floor_le ht
      have hk_lt : t < (k:ℝ) + 1 := by simpa using Nat.lt_floor_add_one t
      rcases eq_or_lt_of_le (by linarith : (0:ℝ) ≤ t - (k:ℝ)) with h0 | h0
      · have htk : t = (k:ℝ) := by linarith
        have hk1 : 1 ≤ k := by
          have hpos : (0:ℝ) < (k:ℝ) := by rw [← htk]; exact h
          exact_mod_cast hpos
        obtain ⟨c', u', hc', hp_src', hu'0, _, hline_ev⟩ := hjunc k hk1
        obtain ⟨T₁, hT₁open, hT₁mem, hT₁sm, hT₁imm⟩ := chartLine_data (n := n) hc' hp_src' hu'0
        rw [htk, hline_ev.mfderiv_eq]
        refine reparam_transfer (f := fun v : ℝ => c'.symm (c' (P k 0) + v • u'))
          (a := fun s : ℝ => s - (k:ℝ)) (x := (k:ℝ)) ?_ ?_ ?_ ?_
        · rw [show (k:ℝ) - (k:ℝ) = 0 from by ring]
          exact (hT₁sm.contMDiffAt (hT₁open.mem_nhds hT₁mem)).mdifferentiableAt (by simp)
        · exact ((contMDiff_id.sub contMDiff_const).contMDiffAt (n := ∞)).mdifferentiableAt (by simp)
        · rw [show (k:ℝ) - (k:ℝ) = 0 from by ring, mfderiv_sub_eq_id]
          exact Function.injective_id
        · rw [show (k:ℝ) - (k:ℝ) = 0 from by ring]
          exact hT₁imm
      · have hmem : Set.Ioo (k:ℝ) ((k:ℝ) + 1) ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨by linarith, hk_lt⟩
        have hev : r =ᶠ[𝓝 t] (fun s : ℝ => P k (s - (k:ℝ))) := by
          filter_upwards [hmem] with s hs
          rw [hr_pos (by linarith [hs.1, (Nat.cast_nonneg k : (0:ℝ) ≤ (k:ℝ))])]
          have hfl : ⌊s⌋₊ = k := Nat.floor_eq_on_Ico k s ⟨le_of_lt hs.1, by simpa using hs.2⟩
          rw [hfl]
        rw [hev.mfderiv_eq]
        refine reparam_transfer (f := P k) (a := fun s : ℝ => s - (k:ℝ)) (x := t) ?_ ?_ ?_ ?_
        · exact ((hsm k).contMDiffAt (x := t - (k:ℝ))).mdifferentiableAt (by simp)
        · exact ((contMDiff_id.sub contMDiff_const).contMDiffAt (n := ∞)).mdifferentiableAt (by simp)
        · rw [mfderiv_sub_eq_id]
          exact Function.injective_id
        · exact himm k (t - (k:ℝ)) (hfloor_mem ht)
  refine ⟨r, ?_, hsmr, hinj_r, hprop, himmr, ?_, ?_⟩
  · intro t ht; exact hr_le ht
  · intro t ht
    rcases eq_or_lt_of_le ht with h | h
    · subst h; rw [hr_zero]; exact Or.inl rfl
    · rw [hr_pos h]
      exact Or.inr (Set.mem_iUnion.mpr ⟨⌊t⌋₊, Set.mem_image_of_mem _ (hfloor_mem (le_of_lt h))⟩)
  · intro t _ he'; exact hr_germ_le he'

end

end Work.Noncompact.CompressionTube
