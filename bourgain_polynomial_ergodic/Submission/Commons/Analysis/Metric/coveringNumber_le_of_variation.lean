import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.MetricSpace.CoveringNumbers

namespace Commons.Analysis.Metric

open scoped BigOperators ENNReal NNReal

variable {E : Type*} [PseudoMetricSpace E]

lemma chain_bound
    (a : ℝ → E) {s : ℝ} (hs : 1 ≤ s) {V : ℝ}
    (hV : ∀ (J : ℕ) (u : Fin (J + 1) → ℝ), StrictMono u →
      (∑ j : Fin J, dist (a (u (Fin.castSucc j))) (a (u (Fin.succ j))) ^ s) ^ ((1:ℝ)/s) ≤ V)
    {ε : ℝ} (hε : 0 < ε) (hVnonneg : 0 ≤ V)
    (t : Finset E) (ht : (t : Set E) ⊆ Set.range a)
    (hsep : Metric.IsSeparated (ε.toNNReal : ℝ≥0∞) (t : Set E)) :
    ((t.card - 1 : ℕ) : ℝ) ≤ (V / ε) ^ s := by
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hεnn : 0 ≤ ε := le_of_lt hε
  have hcoe : (ε.toNNReal : ℝ≥0∞) = ENNReal.ofReal ε := by
    rw [Real.toNNReal_of_nonneg hεnn, ENNReal.ofReal_eq_coe_nnreal hεnn]
  by_cases hcard0 : t.card = 0
  · have h0 : ((t.card - 1 : ℕ) : ℝ) = 0 := by simp [hcard0]
    rw [h0]
    exact Real.rpow_nonneg (div_nonneg hVnonneg hεnn) s
  obtain hm : 1 ≤ t.card := by omega
  have hcast : (t.card - 1) + 1 = t.card := by omega
  let g : ↥(t : Set E) → ℝ := fun y => (ht y.2).choose
  have hg : ∀ y : ↥(t : Set E), a (g y) = (y : E) := fun y => (ht y.2).choose_spec
  have hg_inj : Function.Injective g := by
    intro y z hyz
    apply Subtype.ext
    calc (y : E) = a (g y) := (hg y).symm
      _ = a (g z) := by rw [hyz]
      _ = (z : E) := hg z
  set img : Finset ℝ := t.attach.image g with himg
  have hcard : img.card = t.card := by
    rw [himg, Finset.card_image_of_injective t.attach hg_inj, Finset.card_attach]
  let v : Fin t.card → ℝ := fun i => img.orderEmbOfFin hcard i
  have hv_mem : ∀ k : Fin t.card, v k ∈ img := fun k => Finset.orderEmbOfFin_mem img hcard k
  have hpre : ∀ k : Fin t.card, ∃ y : ↥(t : Set E), g y = v k := fun k => by
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp (hv_mem k)
    exact ⟨y, hy⟩
  let pre : Fin t.card → ↥(t : Set E) := fun k => (hpre k).choose
  have hpre_spec : ∀ k, g (pre k) = v k := fun k => (hpre k).choose_spec
  have hpre_inj : Function.Injective pre := by
    intro k l hkl
    apply (img.orderEmbOfFin hcard).injective
    change v k = v l
    rw [← hpre_spec k, ← hpre_spec l, hkl]
  let u : Fin ((t.card - 1) + 1) → ℝ := fun i => v (Fin.cast hcast i)
  have hu_mono : StrictMono u := by
    intro i j hij
    show v (Fin.cast hcast i) < v (Fin.cast hcast j)
    apply (img.orderEmbOfFin hcard).strictMono
    rw [Fin.lt_def] at hij ⊢
    simpa [Fin.val_cast] using hij
  have hVapp := hV (t.card - 1) u hu_mono
  have key : ∀ j : Fin (t.card - 1),
      ε ^ s ≤ dist (a (u (Fin.castSucc j))) (a (u (Fin.succ j))) ^ s := by
    intro j
    let k : Fin t.card := Fin.cast hcast (Fin.castSucc j)
    let l : Fin t.card := Fin.cast hcast (Fin.succ j)
    have hkl : k ≠ l := by
      intro h
      have hv : k.val = l.val := by rw [h]
      simp only [k, l, Fin.val_cast, Fin.val_castSucc, Fin.val_succ] at hv
      omega
    show ε ^ s ≤ dist (a (v k)) (a (v l)) ^ s
    have hne : (pre k : E) ≠ (pre l : E) := fun h => hkl (hpre_inj (Subtype.ext h))
    have hsep' : (ε.toNNReal : ℝ≥0∞) < edist (pre k) (pre l) :=
      hsep (pre k).2 (pre l).2 hne
    have hlt : ENNReal.ofReal ε < ENNReal.ofReal (dist (pre k) (pre l)) := by
      rw [hcoe, edist_dist] at hsep'
      exact hsep'
    have hle : ε ≤ dist (pre k) (pre l) :=
      le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hεnn).mp hlt)
    have hdv : dist (a (v k)) (a (v l)) = dist (pre k) (pre l) := by
      rw [← hpre_spec k, ← hpre_spec l]
      simp only [hg]
      rfl
    rw [hdv]
    exact Real.rpow_le_rpow hεnn hle hs_pos.le
  have hs_sum : ((t.card - 1 : ℕ) : ℝ) * ε ^ s ≤
      ∑ j : Fin (t.card - 1), dist (a (u (Fin.castSucc j))) (a (u (Fin.succ j))) ^ s := by
    have h := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin (t.card - 1)))
      (fun j => dist (a (u (Fin.castSucc j))) (a (u (Fin.succ j))) ^ s) (ε ^ s)
      (fun j _ => key j)
    simpa [Fintype.card_fin, nsmul_eq_mul] using h
  have hmul : (((t.card - 1 : ℕ) : ℝ) * ε ^ s) ^ ((1:ℝ)/s)
      = ((t.card - 1 : ℕ) : ℝ) ^ ((1:ℝ)/s) * ε := by
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hεnn s),
      ← Real.rpow_mul hεnn s ((1:ℝ)/s), mul_one_div, div_self (ne_of_gt hs_pos), Real.rpow_one]
  have hsq : ((t.card - 1 : ℕ) : ℝ) ^ ((1:ℝ)/s) * ε ≤ V := by
    have h2 := le_trans (Real.rpow_le_rpow
      (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hεnn s)) hs_sum
      (one_div_nonneg.mpr hs_pos.le)) hVapp
    rwa [hmul] at h2
  have hroot : ((t.card - 1 : ℕ) : ℝ) ^ ((1:ℝ)/s) ≤ V / ε :=
    (le_div_iff₀ hε).mpr hsq
  calc ((t.card - 1 : ℕ) : ℝ)
      = (((t.card - 1 : ℕ) : ℝ) ^ ((1:ℝ)/s)) ^ s := by
        rw [← Real.rpow_mul (Nat.cast_nonneg _) ((1:ℝ)/s) s,
          one_div_mul_cancel (ne_of_gt hs_pos), Real.rpow_one]
    _ ≤ (V / ε) ^ s :=
        Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) hroot hs_pos.le

lemma finite_sep_ncard_le
    (a : ℝ → E) {s : ℝ} (hs : 1 ≤ s) {V : ℝ}
    (hV : ∀ (J : ℕ) (u : Fin (J + 1) → ℝ), StrictMono u →
      (∑ j : Fin J, dist (a (u (Fin.castSucc j))) (a (u (Fin.succ j))) ^ s) ^ ((1:ℝ)/s) ≤ V)
    {ε : ℝ} (hε : 0 < ε) (hVnonneg : 0 ≤ V)
    (t : Set E) (htfin : t.Finite) (ht : t ⊆ Set.range a)
    (hsep : Metric.IsSeparated (ε.toNNReal : ℝ≥0∞) t) :
    t.ncard ≤ ⌊(V / ε) ^ s⌋₊ + 1 := by
  by_contra hcon
  rw [not_le] at hcon
  have hchain := chain_bound a hs hV hε hVnonneg htfin.toFinset
      (by rw [htfin.coe_toFinset]; exact ht)
      (by rw [htfin.coe_toFinset]; exact hsep)
  rw [← Set.ncard_eq_toFinset_card t htfin] at hchain
  have hle : ⌊(V / ε) ^ s⌋₊ + 2 ≤ t.ncard := by omega
  have hcast2 : ((t.ncard - 1 : ℕ) : ℝ) = (t.ncard : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ t.ncard)]; norm_num
  have hxlt : (V / ε) ^ s < ((⌊(V / ε) ^ s⌋₊ + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  have hge : ((⌊(V / ε) ^ s⌋₊ + 1 : ℕ) : ℝ) ≤ (t.ncard : ℝ) - 1 := by
    have h1 : (⌊(V / ε) ^ s⌋₊ + 1 : ℕ) ≤ t.ncard - 1 := by omega
    have h2 : ((⌊(V / ε) ^ s⌋₊ + 1 : ℕ) : ℝ) ≤ ((t.ncard - 1 : ℕ) : ℝ) := by exact_mod_cast h1
    linarith [hcast2]
  linarith [hchain]

lemma packingNumber_le
    (a : ℝ → E) {s : ℝ} (hs : 1 ≤ s) {V : ℝ}
    (hV : ∀ (J : ℕ) (u : Fin (J + 1) → ℝ), StrictMono u →
      (∑ j : Fin J, dist (a (u (Fin.castSucc j))) (a (u (Fin.succ j))) ^ s) ^ ((1:ℝ)/s) ≤ V)
    {ε : ℝ} (hε : 0 < ε) (hVnonneg : 0 ≤ V) :
    Metric.packingNumber ε.toNNReal (Set.range a) ≤ (⌊(V / ε) ^ s⌋₊ + 1 : ℕ) := by
  rw [Metric.packingNumber]
  refine iSup_le fun C => iSup_le fun hCsub => iSup_le fun hCsep => ?_
  rw [Set.encard_le_coe_iff_finite_ncard_le]
  refine ⟨?_, ?_⟩
  · by_contra hcon
    rw [Set.not_finite] at hcon
    obtain ⟨t, htC, htfin, htcard⟩ := hcon.exists_subset_ncard_eq (⌊(V / ε) ^ s⌋₊ + 2)
    have hble := finite_sep_ncard_le a hs hV hε hVnonneg t htfin (htC.trans hCsub)
      (Metric.IsSeparated.subset htC hCsep)
    omega
  · by_contra hcon
    rw [not_le] at hcon
    have hn : ⌊(V / ε) ^ s⌋₊ + 2 ≤ C.ncard := by omega
    obtain ⟨t, htC, htcard⟩ := Set.exists_subset_card_eq hn
    have htfin : t.Finite := Set.finite_of_ncard_ne_zero (by rw [htcard]; omega)
    have hble := finite_sep_ncard_le a hs hV hε hVnonneg t htfin (htC.trans hCsub)
      (Metric.IsSeparated.subset htC hCsep)
    omega

theorem coveringNumber_le_of_variation {E : Type*} [PseudoMetricSpace E]
    (a : ℝ → E) (s : ℝ) (hs : 1 ≤ s) (V : ℝ)
    (hV : ∀ (J : ℕ) (u : Fin (J + 1) → ℝ), StrictMono u →
      (∑ j : Fin J, dist (a (u (Fin.castSucc j))) (a (u (Fin.succ j))) ^ s) ^ ((1:ℝ)/s) ≤ V)
    {ε : ℝ} (hε : 0 < ε)
    (hfin : Metric.coveringNumber ε.toNNReal (Set.range a) ≠ ⊤) :
    ENNReal.ofReal ε * (((Metric.coveringNumber ε.toNNReal (Set.range a) : ℕ∞) : ENNReal) - 1) ^ ((1:ℝ)/s)
      ≤ ENNReal.ofReal (2 ^ ((1:ℝ)/s) * (V + ε)) := by
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hεnn : 0 ≤ ε := le_of_lt hε
  have hVnonneg : 0 ≤ V := by
    have h := hV 0 (fun _ => (0:ℝ)) (fun i j hij => absurd hij (by omega))
    have h0 : (∑ j : Fin 0,
        dist (a ((fun _ => (0:ℝ)) (Fin.castSucc j))) (a ((fun _ => (0:ℝ)) (Fin.succ j))) ^ s) = 0 := by simp
    rw [h0] at h
    exact le_trans (Real.rpow_nonneg le_rfl ((1:ℝ)/s)) h
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp hfin
  have hclepack := Metric.coveringNumber_le_packingNumber ε.toNNReal (Set.range a)
  have hpack := packingNumber_le a hs hV hε hVnonneg
  have hNK : N ≤ ⌊(V / ε) ^ s⌋₊ + 1 := by
    have : (N : ℕ∞) ≤ (⌊(V / ε) ^ s⌋₊ + 1 : ℕ) := by
      rw [hN]; exact le_trans hclepack hpack
    exact (ENat.natCast_le_natCast).mp this
  have hNsub : ((N - 1 : ℕ) : ℝ) ≤ (V / ε) ^ s := by
    have h1 : N - 1 ≤ ⌊(V / ε) ^ s⌋₊ := by omega
    have h2 : ((N - 1 : ℕ) : ℝ) ≤ (⌊(V / ε) ^ s⌋₊ : ℝ) := by exact_mod_cast h1
    have h3 : (⌊(V / ε) ^ s⌋₊ : ℝ) ≤ (V / ε) ^ s :=
      Nat.floor_le (Real.rpow_nonneg (div_nonneg hVnonneg hεnn) s)
    linarith
  have hVdiv : 0 ≤ V / ε := div_nonneg hVnonneg hεnn
  have hroot : ((N - 1 : ℕ) : ℝ) ^ ((1:ℝ)/s) ≤ V / ε := by
    calc ((N - 1 : ℕ) : ℝ) ^ ((1:ℝ)/s)
        ≤ ((V / ε) ^ s) ^ ((1:ℝ)/s) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hNsub (one_div_nonneg.mpr hs_pos.le)
      _ = V / ε := by
          rw [← Real.rpow_mul hVdiv s ((1:ℝ)/s), mul_one_div, div_self (ne_of_gt hs_pos), Real.rpow_one]
  have hreal : ε * ((N - 1 : ℕ) : ℝ) ^ ((1:ℝ)/s) ≤ 2 ^ ((1:ℝ)/s) * (V + ε) := by
    have h1 : ε * ((N - 1 : ℕ) : ℝ) ^ ((1:ℝ)/s) ≤ V := by
      calc ε * ((N - 1 : ℕ) : ℝ) ^ ((1:ℝ)/s) ≤ ε * (V / ε) := mul_le_mul_of_nonneg_left hroot hεnn
        _ = V := by field_simp
    have h2 : (1:ℝ) ≤ 2 ^ ((1:ℝ)/s) := Real.one_le_rpow (by norm_num) (one_div_nonneg.mpr hs_pos.le)
    have h3 : V ≤ 2 ^ ((1:ℝ)/s) * V := le_mul_of_one_le_left hVnonneg h2
    have h4 : 2 ^ ((1:ℝ)/s) * V ≤ 2 ^ ((1:ℝ)/s) * (V + ε) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hεnn) (Real.rpow_nonneg (by norm_num) _)
    linarith [h1, h3, h4]
  have hcast : (((N : ℕ∞) : ENNReal) - 1) = ENNReal.ofReal ((N - 1 : ℕ) : ℝ) := by
    have h1 : (((N : ℕ∞) : ENNReal)) = (N : ENNReal) := by simp
    rw [h1, show (1:ENNReal) = ((1:ℕ):ENNReal) by simp, ← ENNReal.natCast_sub N 1,
      ENNReal.ofReal_natCast]
  have hrpow : (ENNReal.ofReal ((N - 1 : ℕ) : ℝ)) ^ ((1:ℝ)/s)
      = ENNReal.ofReal (((N - 1 : ℕ) : ℝ) ^ ((1:ℝ)/s)) :=
    ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (one_div_nonneg.mpr hs_pos.le)
  rw [← hN]
  calc ENNReal.ofReal ε * ((((N : ℕ∞) : ENNReal)) - 1) ^ ((1:ℝ)/s)
      = ENNReal.ofReal ε * ENNReal.ofReal (((N - 1 : ℕ) : ℝ) ^ ((1:ℝ)/s)) := by rw [hcast, hrpow]
    _ = ENNReal.ofReal (ε * (((N - 1 : ℕ) : ℝ) ^ ((1:ℝ)/s))) := (ENNReal.ofReal_mul hεnn).symm
    _ ≤ ENNReal.ofReal (2 ^ ((1:ℝ)/s) * (V + ε)) := ENNReal.ofReal_le_ofReal hreal

end Commons.Analysis.Metric