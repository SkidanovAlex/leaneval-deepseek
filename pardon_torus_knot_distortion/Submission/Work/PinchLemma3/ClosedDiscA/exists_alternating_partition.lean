import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.PinchLemma3.ClosedDiscA.exists_separation
import Submission.Work.PinchLemma3.ClosedDiscA.exists_blocks

/-!
# The alternating partition of a closed curve lying in the union of two open regions

`Work.PinchLemma3.ClosedDiscA.exists_alternating_partition`: a closed curve `γ` of a parametrised
torus whose image lies in the union of two regions `A`, `B` that are open in the surface is either
entirely in `A`, entirely in `B`, or admits a finite monochromatic *alternating* partition: there
are `k ≥ 1` and `0 ≤ s 0 < s 1 < ⋯ < s (2k) = s 0 + 2π` with

* `γ t ∈ A` for `t ∈ [s (2j), s (2j+1)]` (`j < k`),
* `γ t ∈ B` for `t ∈ [s (2j+1), s (2j+2)]` (`j < k`).

The proof pulls `U = γ⁻¹ A` and `V = γ⁻¹ B` back to `ℝ`; these are open and `2π`-periodic and cover
`ℝ`.  If both complements are nonempty they are nonempty closed disjoint `2π`-periodic sets, hence
separated by some `δ > 0` (`exists_separation`), and a grid of mesh `h = 2π/N < δ` subdivides one
period into intervals each lying in `U` or in `V`.  The labels of the grid intervals form a periodic
binary word whose cyclic monochromatic blocks are extracted by `exists_blocks`; the grid points at
the block boundaries give the required `s`.  Both auxiliary modules are proved separately.

The results are stated and proved for an arbitrary `ParamTorus`; specialising to the standard torus
recovers Pardon's setting.
-/

open Set LeanEval.KnotTheory.PardonDistortion

namespace Work.PinchLemma3.ClosedDiscA

noncomputable section

theorem mem_add_nat_mul_two_pi {S : Set ℝ} (h : ∀ t, t + 2 * Real.pi ∈ S ↔ t ∈ S)
    (t : ℝ) (n : ℕ) : t + (n : ℝ) * (2 * Real.pi) ∈ S ↔ t ∈ S := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hrepr : t + ((m + 1 : ℕ) : ℝ) * (2 * Real.pi)
          = (t + (m : ℝ) * (2 * Real.pi)) + 2 * Real.pi := by push_cast; ring
      rw [hrepr, h]
      exact ih

theorem mem_add_int_mul_two_pi {S : Set ℝ} (h : ∀ t, t + 2 * Real.pi ∈ S ↔ t ∈ S)
    (t : ℝ) (n : ℤ) : t + (n : ℝ) * (2 * Real.pi) ∈ S ↔ t ∈ S := by
  rcases lt_or_ge n 0 with hn | hn
  · have hpos : 0 < -n := by omega
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hpos)
    have hn' : n = -(m : ℤ) := by omega
    have hcast : ((n:ℤ) : ℝ) = -((m:ℕ):ℝ) := by rw [hn']; push_cast; ring
    rw [hcast]
    have hkey := mem_add_nat_mul_two_pi h (t + (-(m:ℝ)) * (2*Real.pi)) m
    have hsimp : t + (-(m:ℝ)) * (2*Real.pi) + (m:ℝ) * (2*Real.pi) = t := by ring
    rw [hsimp] at hkey
    exact hkey.symm
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hn
    have hcast : ((n:ℤ) : ℝ) = ((m:ℕ):ℝ) := by rw [hm]; push_cast; ring
    rw [hcast]
    exact mem_add_nat_mul_two_pi h t m

/-- **The partition lemma.**  An open `2π`-periodic cover of `ℝ` by two properly smaller open sets
admits a finite monochromatic alternating partition of one period. -/
theorem exists_partition_of_periodic_open_cover
    {U V : Set ℝ} (hUo : IsOpen U) (hVo : IsOpen V)
    (hperU : ∀ t, t + 2 * Real.pi ∈ U ↔ t ∈ U)
    (hperV : ∀ t, t + 2 * Real.pi ∈ V ↔ t ∈ V)
    (hcov : U ∪ V = univ)
    (hUne : (Uᶜ).Nonempty) (hVne : (Vᶜ).Nonempty) :
    ∃ (k : ℕ) (_ : 0 < k) (s : ℕ → ℝ),
      s 0 ∈ Set.Ico 0 (2 * Real.pi) ∧ s (2 * k) = s 0 + 2 * Real.pi ∧
      (∀ i j, i ≤ 2 * k → j ≤ 2 * k → i < j → s i < s j) ∧
      (∀ j, j < k → ∀ t, s (2 * j) ≤ t → t ≤ s (2 * j + 1) → t ∈ U) ∧
      (∀ j, j < k → ∀ t, s (2 * j + 1) ≤ t → t ≤ s (2 * j + 2) → t ∈ V) := by
  classical
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  -- P = Vᶜ, Q = Uᶜ
  have hPc : IsClosed (Vᶜ) := isClosed_compl_iff.mpr hVo
  have hQc : IsClosed (Uᶜ) := isClosed_compl_iff.mpr hUo
  have hPp : ∀ t, t + 2*Real.pi ∈ Vᶜ ↔ t ∈ Vᶜ := by
    intro t; rw [Set.mem_compl_iff, Set.mem_compl_iff, hperV t]
  have hQp : ∀ t, t + 2*Real.pi ∈ Uᶜ ↔ t ∈ Uᶜ := by
    intro t; rw [Set.mem_compl_iff, Set.mem_compl_iff, hperU t]
  have hdisj : Disjoint (Vᶜ) (Uᶜ) := by
    rw [Set.disjoint_left]
    intro t htV htU
    have : t ∈ U ∪ V := by rw [hcov]; trivial
    rcases this with h | h
    · exact htU h
    · exact htV h
  obtain ⟨δ, hδpos, hsep⟩ := exists_separation hPc hQc hPp hQp hVne hUne hdisj
  -- choose N
  obtain ⟨N, hNgt⟩ := exists_nat_gt (2 * Real.pi / δ)
  have hδne : δ ≠ 0 := ne_of_gt hδpos
  have hNpos : 0 < N := by
    by_contra hcon
    have : N = 0 := Nat.eq_zero_of_not_pos hcon
    rw [this] at hNgt; push_cast at hNgt
    have : 2*Real.pi/δ ≤ 0 := le_of_lt hNgt
    have : 0 < 2*Real.pi/δ := by positivity
    linarith
  set h : ℝ := 2*Real.pi/N with hh
  have hhpos : 0 < h := by rw [hh]; positivity
  have hhδ : h < δ := by
    rw [hh, div_lt_iff₀ (by positivity : (0:ℝ) < (N:ℝ))]
    have : (2*Real.pi/δ) < N := hNgt
    rw [div_lt_iff₀ hδpos] at this
    linarith
  have hNh : (N:ℝ) * h = 2*Real.pi := by
    rw [hh]; field_simp
  -- grid function
  set G : ℕ → ℝ := fun m => (m:ℝ) * h with hGdef
  have hGN : ∀ m : ℕ, G (m + N) = G m + 2*Real.pi := by
    intro m
    simp only [hGdef]
    rw [Nat.cast_add, add_mul]
    have : (N:ℝ) * h = 2*Real.pi := hNh
    linarith [this]
  -- the label function
  set ℓ : ℕ → Bool := fun m => if ((Set.Icc (G m) (G (m+1)) : Set ℝ) ∩ Uᶜ).Nonempty then false else true
    with hℓdef
  have hℓtrue : ∀ m, ℓ m = true ↔ ¬ ((Set.Icc (G m) (G (m+1)) : Set ℝ) ∩ Uᶜ).Nonempty := by
    intro m; simp only [hℓdef]; by_cases hc : ((Set.Icc (G m) (G (m+1)) : Set ℝ) ∩ Uᶜ).Nonempty <;> simp [hc]
  have hℓfalse : ∀ m, ℓ m = false ↔ ((Set.Icc (G m) (G (m+1)) : Set ℝ) ∩ Uᶜ).Nonempty := by
    intro m; simp only [hℓdef]; by_cases hc : ((Set.Icc (G m) (G (m+1)) : Set ℝ) ∩ Uᶜ).Nonempty <;> simp [hc]
  -- periodicity of ℓ
  have hperℓ : ∀ i, ℓ (i+N) = ℓ i := by
    intro i
    have hiff : ((Set.Icc (G (i+N)) (G (i+N+1)) : Set ℝ) ∩ Uᶜ).Nonempty
        ↔ ((Set.Icc (G i) (G (i+1)) : Set ℝ) ∩ Uᶜ).Nonempty := by
      have e1 : G (i+N) = G i + 2*Real.pi := hGN i
      have e2 : G (i+N+1) = G (i+1) + 2*Real.pi := by
        have := hGN (i+1); simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      rw [e1, e2]
      constructor
      · rintro ⟨x, hx, hxU⟩
        refine ⟨x - 2*Real.pi, ?_, ?_⟩
        · rcases hx with ⟨hx1, hx2⟩
          exact ⟨by linarith, by linarith⟩
        · rw [Set.mem_compl_iff] at hxU ⊢
          intro hcon
          apply hxU
          have := (hperU (x - 2*Real.pi)).mpr hcon
          simpa using this
      · rintro ⟨x, hx, hxU⟩
        refine ⟨x + 2*Real.pi, ?_, ?_⟩
        · rcases hx with ⟨hx1, hx2⟩
          exact ⟨by linarith, by linarith⟩
        · rw [Set.mem_compl_iff] at hxU ⊢
          intro hcon
          apply hxU
          exact (hperU x).mp hcon
    simp only [hℓdef]
    rw [if_congr hiff rfl rfl]
  -- strict increase of G
  have hGstrict : ∀ a b : ℕ, a < b → G a < G b := by
    intro a b hab
    simp only [hGdef]
    have hab' : (a:ℝ) < (b:ℝ) := by exact_mod_cast hab
    exact mul_lt_mul_of_pos_right hab' hhpos
  have hGle : ∀ a b : ℕ, a ≤ b → G a ≤ G b := fun a b h => by
    rcases lt_or_eq_of_le h with h' | h'
    · exact le_of_lt (hGstrict a b h')
    · rw [h']
  -- both labels occur
  have hGstep : ∀ m : ℕ, G (m+1) = G m + h := by
    intro m; simp only [hGdef]; push_cast; ring
  have hGNval : G N = 2 * Real.pi := by simp only [hGdef]; exact hNh
  have hgrid_cover : ∀ (t : ℝ), 0 ≤ t → t ≤ G N → ∃ i, i < N ∧ G i ≤ t ∧ t ≤ G (i+1) := by
    intro t ht0 htN
    have hdnn : 0 ≤ t / h := div_nonneg ht0 (le_of_lt hhpos)
    have h1le : ((Nat.floor (t/h) : ℕ) : ℝ) ≤ t / h := Nat.floor_le hdnn
    have h1lt : t / h < ((Nat.floor (t/h) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one (t/h)
    have hA : G (Nat.floor (t/h)) ≤ t := by
      have hle := mul_le_mul_of_nonneg_right h1le (le_of_lt hhpos)
      rw [div_mul_cancel₀ t (ne_of_gt hhpos)] at hle
      simpa [hGdef] using hle
    have hB : t < G (Nat.floor (t/h) + 1) := by
      have hlt := mul_lt_mul_of_pos_right h1lt hhpos
      rw [div_mul_cancel₀ t (ne_of_gt hhpos)] at hlt
      simpa [hGdef, Nat.cast_add, Nat.cast_one] using hlt
    have hbm : G (Nat.floor (t/h)) ≤ G N := le_trans hA htN
    have hleN : Nat.floor (t/h) ≤ N := by
      have h1 : ((Nat.floor (t/h) : ℕ) : ℝ) ≤ (N:ℝ) := by
        have := hbm; simp only [hGdef] at this
        exact le_of_mul_le_mul_right this hhpos
      exact_mod_cast h1
    rcases lt_or_eq_of_le hleN with hlt | heq
    · exact ⟨Nat.floor (t/h), hlt, hA, le_of_lt hB⟩
    · have hNle : G N ≤ t := by rw [← heq]; exact hA
      refine ⟨N-1, by omega, ?_, ?_⟩
      · have h1 : G (N-1) ≤ G N := hGle (N-1) N (by omega)
        linarith
      · rw [Nat.sub_add_cancel hNpos]
        exact htN
  -- P meets one grid interval
  have hexP : ∃ i, i < N ∧ ℓ i = true := by
    obtain ⟨p, hpP⟩ := hVne
    set p' : ℝ := p - ((⌊p / (2*Real.pi)⌋ : ℤ) : ℝ) * (2*Real.pi) with hp'def
    have hp'P : p' ∈ Vᶜ := by
      have h := (mem_add_int_mul_two_pi hPp p (-⌊p/(2*Real.pi)⌋)).mpr hpP
      have hcast : p + ((-⌊p/(2*Real.pi)⌋ : ℤ) : ℝ) * (2*Real.pi)
          = p - ((⌊p/(2*Real.pi)⌋ : ℤ) : ℝ) * (2*Real.pi) := by push_cast; ring
      rw [hcast] at h
      exact h
    have hp'ge : 0 ≤ p' := by
      have h1 := Int.floor_le (p / (2*Real.pi))
      have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt h2pi)
      rw [div_mul_cancel₀ p (ne_of_gt h2pi)] at h2
      simp only [hp'def]; linarith
    have hp'lt : p' < 2*Real.pi := by
      have h1 := Int.lt_floor_add_one (p / (2*Real.pi))
      have h2 := mul_lt_mul_of_pos_right h1 h2pi
      rw [div_mul_cancel₀ p (ne_of_gt h2pi)] at h2
      simp only [hp'def]; linarith
    obtain ⟨i, hiN, hi1, hi2⟩ := hgrid_cover p' hp'ge (by rw [hGNval]; exact le_of_lt hp'lt)
    refine ⟨i, hiN, ?_⟩
    rw [hℓtrue i]
    rintro ⟨q, hq, hqU⟩
    have hle : |p' - q| ≤ h := by
      rcases hq with ⟨hq1, hq2⟩
      rw [abs_sub_le_iff]
      constructor
      · linarith [hGstep i, hi2, hq1]
      · linarith [hGstep i, hi1, hq2]
    have hδ := hsep p' hp'P q hqU
    linarith
  -- Q meets one grid interval
  have hexQ : ∃ j, j < N ∧ ℓ j = false := by
    obtain ⟨q, hqQ⟩ := hUne
    set q' : ℝ := q - ((⌊q / (2*Real.pi)⌋ : ℤ) : ℝ) * (2*Real.pi) with hq'def
    have hq'Q : q' ∈ Uᶜ := by
      have h := (mem_add_int_mul_two_pi hQp q (-⌊q/(2*Real.pi)⌋)).mpr hqQ
      have hcast : q + ((-⌊q/(2*Real.pi)⌋ : ℤ) : ℝ) * (2*Real.pi)
          = q - ((⌊q/(2*Real.pi)⌋ : ℤ) : ℝ) * (2*Real.pi) := by push_cast; ring
      rw [hcast] at h
      exact h
    have hq'ge : 0 ≤ q' := by
      have h1 := Int.floor_le (q / (2*Real.pi))
      have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt h2pi)
      rw [div_mul_cancel₀ q (ne_of_gt h2pi)] at h2
      simp only [hq'def]; linarith
    have hq'lt : q' < 2*Real.pi := by
      have h1 := Int.lt_floor_add_one (q / (2*Real.pi))
      have h2 := mul_lt_mul_of_pos_right h1 h2pi
      rw [div_mul_cancel₀ q (ne_of_gt h2pi)] at h2
      simp only [hq'def]; linarith
    obtain ⟨j, hjN, hj1, hj2⟩ := hgrid_cover q' hq'ge (by rw [hGNval]; exact le_of_lt hq'lt)
    refine ⟨j, hjN, ?_⟩
    rw [hℓfalse j]
    exact ⟨q', ⟨hj1, hj2⟩, hq'Q⟩
  have hex : ∃ i j, i < N ∧ j < N ∧ ℓ i ≠ ℓ j := by
    obtain ⟨i, hiN, hi⟩ := hexP
    obtain ⟨j, hjN, hj⟩ := hexQ
    exact ⟨i, j, hiN, hjN, by rw [hi, hj]; decide⟩
  obtain ⟨k, hk, e, hemono, he0lt, he2k, helab, heblk⟩ := exists_blocks hNpos ℓ hperℓ hex
  -- monotonicity of e
  have hestrict : ∀ i j, i < j → j ≤ 2*k → e i < e j := by
    intro i j
    induction j with
    | zero => intro hij; omega
    | succ m ih =>
        intro hij hm
        rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hlt | heq
        · have hm' : m ≤ 2*k := by omega
          exact lt_trans (ih hlt hm') (hemono m (by omega))
        · subst heq; exact hemono i (by omega)
  -- the grid index lemma
  have hgrididx : ∀ (a b : ℕ), a < b → ∀ t : ℝ, G a ≤ t → t ≤ G b →
      ∃ m, a ≤ m ∧ m < b ∧ G m ≤ t ∧ t ≤ G (m+1) := by
    intro a b hab t ha hb
    have ht0 : 0 ≤ t := by
      have h0 : G 0 ≤ G a := hGle 0 a (Nat.zero_le a)
      have : G 0 ≤ t := le_trans h0 ha
      simpa [hGdef] using this
    have hdnn : 0 ≤ t / h := div_nonneg ht0 (le_of_lt hhpos)
    have h1le : ((Nat.floor (t/h) : ℕ) : ℝ) ≤ t / h := Nat.floor_le hdnn
    have h1lt : t / h < ((Nat.floor (t/h) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one (t/h)
    have hA : G (Nat.floor (t/h)) ≤ t := by
      have hle := mul_le_mul_of_nonneg_right h1le (le_of_lt hhpos)
      rw [div_mul_cancel₀ t (ne_of_gt hhpos)] at hle
      simpa [hGdef] using hle
    have hB : t < G (Nat.floor (t/h) + 1) := by
      have hlt := mul_lt_mul_of_pos_right h1lt hhpos
      rw [div_mul_cancel₀ t (ne_of_gt hhpos)] at hlt
      simpa [hGdef, Nat.cast_add, Nat.cast_one] using hlt
    have hbm0 : G (Nat.floor (t/h)) ≤ G b := le_trans hA hb
    have hbm0' : Nat.floor (t/h) ≤ b := by
      have h1 : ((Nat.floor (t/h) : ℕ) : ℝ) ≤ (b:ℝ) := by
        have := hbm0; simp only [hGdef] at this
        exact le_of_mul_le_mul_right this hhpos
      exact_mod_cast h1
    have ham0 : a ≤ Nat.floor (t/h) := by
      have h1 : (a:ℝ)*h < (((Nat.floor (t/h) : ℕ) : ℝ) + 1)*h := by
        have ha' : (a:ℝ)*h ≤ t := by simpa [hGdef] using ha
        have hB' : t < (((Nat.floor (t/h) : ℕ) : ℝ) + 1)*h := by
          simpa [hGdef, Nat.cast_add, Nat.cast_one] using hB
        linarith
      have h2 : (a:ℝ) < ((Nat.floor (t/h):ℕ):ℝ) + 1 := lt_of_mul_lt_mul_right h1 (le_of_lt hhpos)
      have h3 : a < Nat.floor (t/h) + 1 := by exact_mod_cast h2
      omega
    rcases lt_or_eq_of_le hbm0' with hlt | heq
    · exact ⟨Nat.floor (t/h), ham0, hlt, hA, le_of_lt hB⟩
    · have hm0b : Nat.floor (t/h) = b := heq
      have hGb : G b ≤ t := by rw [← hm0b]; exact hA
      refine ⟨b-1, by omega, by omega, ?_, ?_⟩
      · have h1 : G (b-1) ≤ G b := hGle (b-1) b (by omega)
        linarith
      · rw [Nat.sub_add_cancel (by omega)]
        exact hb
  -- grid interval membership
  have hgridU : ∀ m, ℓ m = true → ∀ t, G m ≤ t → t ≤ G (m+1) → t ∈ U := by
    intro m hm t ht1 ht2
    rw [hℓtrue m] at hm
    by_contra ht
    exact hm ⟨t, ⟨ht1, ht2⟩, ht⟩
  have hgridV : ∀ m, ℓ m = false → ∀ t, G m ≤ t → t ≤ G (m+1) → t ∈ V := by
    intro m hm t ht1 ht2
    rw [hℓfalse m] at hm
    obtain ⟨q, hq, hqU⟩ := hm
    by_contra ht
    have hδ := hsep t ht q hqU
    have hle : |t - q| ≤ h := by
      rcases hq with ⟨hq1, hq2⟩
      rw [abs_sub_le_iff]
      constructor
      · linarith [hGstep m, ht2, hq1]
      · linarith [hGstep m, ht1, hq2]
    linarith
  -- block membership
  have hblockU : ∀ i, i < 2*k → ℓ (e i) = true → ∀ t, G (e i) ≤ t → t ≤ G (e (i+1)) → t ∈ U := by
    intro i hi hli t ht1 ht2
    obtain ⟨m, hm1, hm2, hm3, hm4⟩ := hgrididx (e i) (e (i+1)) (hemono i hi) t ht1 ht2
    exact hgridU m (by rw [heblk i hi m hm1 hm2]; exact hli) t hm3 hm4
  have hblockV : ∀ i, i < 2*k → ℓ (e i) = false → ∀ t, G (e i) ≤ t → t ≤ G (e (i+1)) → t ∈ V := by
    intro i hi hli t ht1 ht2
    obtain ⟨m, hm1, hm2, hm3, hm4⟩ := hgrididx (e i) (e (i+1)) (hemono i hi) t ht1 ht2
    exact hgridV m (by rw [heblk i hi m hm1 hm2]; exact hli) t hm3 hm4
  -- shift
  set mm : ℤ := ⌊G (e 0) / (2*Real.pi)⌋ with hmm
  have hmm0 : (mm:ℝ) * (2*Real.pi) ≤ G (e 0) := by
    have := Int.floor_le (G (e 0) / (2*Real.pi))
    rw [hmm]
    have := mul_le_mul_of_nonneg_right this (le_of_lt h2pi)
    rwa [div_mul_cancel₀ _ (ne_of_gt h2pi)] at this
  have hmm1 : G (e 0) < ((mm:ℝ) + 1) * (2*Real.pi) := by
    have := Int.lt_floor_add_one (G (e 0) / (2*Real.pi))
    rw [hmm]
    have := mul_lt_mul_of_pos_right this h2pi
    rwa [div_mul_cancel₀ _ (ne_of_gt h2pi)] at this
  refine ⟨k, hk, fun n => G (e n) - (mm:ℝ)*(2*Real.pi), ?_, ?_, ?_, ?_, ?_⟩
  · -- s 0 ∈ Ico 0 (2π)
    constructor
    · linarith
    · linarith
  · -- s (2k) = s 0 + 2π
    have h2k : G (e (2*k)) = G (e 0) + 2*Real.pi := by
      rw [he2k, hGN]
    linarith
  · -- strict monotone
    intro i j hi hj hij
    have h1 : G (e i) < G (e j) := hGstrict _ _ (hestrict i j hij hj)
    linarith
  · -- A-arcs
    intro j hj t ht1 ht2
    have h2j : 2*j < 2*k := by omega
    have hEven : Even (2*j) := ⟨j, by ring⟩
    have hli : ℓ (e (2*j)) = true := (helab (2*j) h2j).mpr hEven
    have htj : G (e (2*j)) ≤ t + (mm:ℝ)*(2*Real.pi) ∧ t + (mm:ℝ)*(2*Real.pi) ≤ G (e (2*j+1)) := by
      constructor <;> linarith [ht1, ht2]
    have hmem := hblockU (2*j) h2j hli _ htj.1 htj.2
    exact (mem_add_int_mul_two_pi hperU t mm).mp (by simpa using hmem)
  · -- B-arcs
    intro j hj t ht1 ht2
    have h2j : 2*j+1 < 2*k := by omega
    have hNotEven : ¬ Even (2*j+1) := by rintro ⟨s, hs⟩; omega
    have hli : ℓ (e (2*j+1)) = false := by
      cases hc : ℓ (e (2*j+1)) with
      | true => exact absurd ((helab (2*j+1) h2j).mp hc) hNotEven
      | false => rfl
    have htj : G (e (2*j+1)) ≤ t + (mm:ℝ)*(2*Real.pi) ∧ t + (mm:ℝ)*(2*Real.pi) ≤ G (e (2*j+2)) := by
      constructor <;> linarith [ht1, ht2]
    have hmem := hblockV (2*j+1) h2j hli _ htj.1 htj.2
    exact (mem_add_int_mul_two_pi hperV t mm).mp (by simpa using hmem)

/-- **The alternating partition of a closed curve lying in the union of two open regions.** -/
theorem exists_alternating_partition {P : Work.CoreTopology.ParamTorus}
    {A B : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hA : Work.SurgeryInvariance.IsOpenInCarrier P A)
    (hB : Work.SurgeryInvariance.IsOpenInCarrier P B)
    (γ : Work.CoreTopology.ClosedCurve P) (hγ : ∀ t : ℝ, γ t ∈ A ∪ B) :
    (∀ t : ℝ, γ t ∈ A) ∨ (∀ t : ℝ, γ t ∈ B) ∨
      ∃ (k : ℕ) (_hk : 0 < k) (s : ℕ → ℝ),
        s 0 ∈ Set.Ico (0 : ℝ) (2 * Real.pi) ∧ s (2 * k) = s 0 + 2 * Real.pi ∧
        (∀ i j : ℕ, i ≤ 2 * k → j ≤ 2 * k → i < j → s i < s j) ∧
        (∀ j : ℕ, j < k → ∀ t : ℝ, s (2 * j) ≤ t → t ≤ s (2 * j + 1) → γ t ∈ A) ∧
        (∀ j : ℕ, j < k → ∀ t : ℝ, s (2 * j + 1) ≤ t → t ≤ s (2 * j + 2) → γ t ∈ B) := by
  classical
  set U : Set ℝ := {t | γ t ∈ A} with hUdef
  set V : Set ℝ := {t | γ t ∈ B} with hVdef
  have hUo : IsOpen U := by
    have hcont : Continuous (fun t : ℝ => (⟨γ t, γ.mem t⟩ : P.carrier)) := γ.cont.subtype_mk _
    have h := hcont.isOpen_preimage (Subtype.val ⁻¹' A) hA
    have hEq : (fun t : ℝ => (⟨γ t, γ.mem t⟩ : P.carrier)) ⁻¹' (Subtype.val ⁻¹' A) = U := by
      ext t; simp [U, Set.mem_preimage]
    rwa [hEq] at h
  have hVo : IsOpen V := by
    have hcont : Continuous (fun t : ℝ => (⟨γ t, γ.mem t⟩ : P.carrier)) := γ.cont.subtype_mk _
    have h := hcont.isOpen_preimage (Subtype.val ⁻¹' B) hB
    have hEq : (fun t : ℝ => (⟨γ t, γ.mem t⟩ : P.carrier)) ⁻¹' (Subtype.val ⁻¹' B) = V := by
      ext t; simp [V, Set.mem_preimage]
    rwa [hEq] at h
  have hperU : ∀ t, t + 2*Real.pi ∈ U ↔ t ∈ U := by
    intro t; simp only [U, Set.mem_ofPred_eq]; rw [γ.periodic t]
  have hperV : ∀ t, t + 2*Real.pi ∈ V ↔ t ∈ V := by
    intro t; simp only [V, Set.mem_ofPred_eq]; rw [γ.periodic t]
  have hcov : U ∪ V = univ := by
    ext t; simp only [U, V, Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ]
    exact ⟨fun _ => trivial, fun _ => hγ t⟩
  by_cases hU : U = univ
  · left; intro t
    have ht : t ∈ U := by rw [hU]; trivial
    simpa [hUdef] using ht
  · by_cases hV : V = univ
    · right; left; intro t
      have ht : t ∈ V := by rw [hV]; trivial
      simpa [hVdef] using ht
    · right; right
      have hUne : (Uᶜ).Nonempty := Set.nonempty_compl.mpr hU
      have hVne : (Vᶜ).Nonempty := Set.nonempty_compl.mpr hV
      obtain ⟨k, hk, s, hs0, hs2k, hmono, hAarc, hBarc⟩ :=
        exists_partition_of_periodic_open_cover hUo hVo hperU hperV hcov hUne hVne
      refine ⟨k, hk, s, hs0, hs2k, hmono, ?_, ?_⟩
      · intro j hj t ht1 ht2
        simpa [hUdef] using hAarc j hj t ht1 ht2
      · intro j hj t ht1 ht2
        simpa [hVdef] using hBarc j hj t ht1 ht2

end
end Work.PinchLemma3.ClosedDiscA
