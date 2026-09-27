import Mathlib
import Submission.Work.Drive.signed_crossing_count
import Submission.Work.Drive.even_ncard_of_periodic_changes
import Submission.Work.Surf.floorCrossSet_parity

/-!
# The parity of the crossing count of the integer levels

For a continuous `G : ℝ → ℝ` with `G (t + 1) = G t + n` (`n : ℤ`) whose integer-level crossings in
`[0,1)` are all transverse (non-zero derivative), the crossings in `[0,1)` are finite and their
number is congruent to `n` modulo `2`.

The proof: the set `W = {t | G t ∈ ℤ}` of *all* integer-level crossings is closed, and every point of
`W ∩ [0,1]` is isolated in `W ∩ [0,1]` (a non-zero derivative at a crossing forces the values on the
two sides to lie strictly inside the neighbouring unit intervals; at `1` one reduces to `0` by
periodicity).  Hence `W ∩ [0,1]` is finite.  The parity is then read off from
`Work.Surf.floorCrossSet_parity` applied to the shifted function `t ↦ G (t + δ)`, where `δ ∈ (0,1)`
is not a crossing: the shift moves the possible crossing at `0` out of the fundamental domain, and by
`1`-periodicity of `W` the number of crossings in `[0,1)` is unchanged.
-/

namespace Work.Surf

open Set
open scoped Topology

noncomputable section

/-- The crossing set of the integer levels of `G` (the set of times at which `G` takes an integer
value). -/
abbrev XS (G : ℝ → ℝ) : Set ℝ := Work.Drive.SCC.CrossSet G

variable {G : ℝ → ℝ} {n : ℤ}

/-! ## Parity bookkeeping -/

/-- Two integers are congruent mod `2` exactly when they have the same parity. -/
lemma modEq_two_iff_odd (a b : ℤ) : a ≡ b [ZMOD 2] ↔ (Odd a ↔ Odd b) := by
  rw [Int.ModEq]
  constructor
  · intro h
    rw [Int.odd_iff, Int.odd_iff, h]
  · intro h
    rw [Int.odd_iff, Int.odd_iff] at h
    rcases Int.emod_two_eq_zero_or_one a with ha | ha <;>
      rcases Int.emod_two_eq_zero_or_one b with hb | hb
    · rw [ha, hb]
    · exact absurd (h.mpr (by rw [hb])) (by rw [ha]; norm_num)
    · exact absurd (h.mp (by rw [ha])) (by rw [hb]; norm_num)
    · rw [ha, hb]

/-- A natural number is odd iff its image in `ℤ` is. -/
lemma odd_natCast (N : ℕ) : Odd (N : ℤ) ↔ Odd N := by
  rw [Int.odd_iff, Nat.odd_iff]
  have h2 : (N : ℤ) % 2 = ((N % 2 : ℕ) : ℤ) := (Int.natCast_emod N 2).symm
  rw [h2]
  constructor <;> intro h <;> exact_mod_cast h

/-! ## Algebraic preliminaries -/

/-- Iterating the periodicity relation: `G (t + k) = G t + k * n`. -/
lemma G_add_int (hper : ∀ t : ℝ, G (t + 1) = G t + (n : ℝ)) (t : ℝ) (k : ℤ) :
    G (t + (k : ℝ)) = G t + (k : ℝ) * (n : ℝ) := by
  have hp' : ∀ s : ℝ, G (s - 1) = G s - (n : ℝ) := by
    intro s
    have h := hper (s - 1)
    rw [sub_add_cancel] at h
    linarith
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
      have h : t + (((i : ℤ) + 1 : ℤ) : ℝ) = (t + ((i : ℤ) : ℝ)) + 1 := by push_cast; ring
      rw [h, hper, ih]; push_cast; ring
  | pred i ih =>
      have h : t + ((-(i : ℤ) - 1 : ℤ) : ℝ) = (t + ((-(i : ℤ) : ℤ) : ℝ)) - 1 := by
        push_cast; ring
      rw [h, hp', ih]; push_cast; ring

/-- The floor of `G` at an integer translate. -/
lemma floor_G_add_int (hper : ∀ t : ℝ, G (t + 1) = G t + (n : ℝ)) (t : ℝ) (k : ℤ) :
    ⌊G (t + (k : ℝ))⌋ = ⌊G t⌋ + k * n := by
  rw [G_add_int hper t k]
  have hcast : (k : ℝ) * (n : ℝ) = ((k * n : ℤ) : ℝ) := by push_cast; ring
  rw [hcast, Int.floor_add_intCast]

/-- A real number strictly inside the unit interval above an integer is not an integer. -/
lemma not_mem_range_of_between {y : ℝ} {m : ℤ} (h1 : (m : ℝ) < y) (h2 : y < (m : ℝ) + 1) :
    ¬ (∃ k : ℤ, y = (k : ℝ)) := by
  rintro ⟨k, hk⟩
  have hfl : ⌊y⌋ = m := Int.floor_eq_iff.mpr ⟨le_of_lt h1, h2⟩
  have hfl2 : ⌊y⌋ = k := by rw [hk]; exact Int.floor_intCast k
  have hy : y = (m : ℝ) := by
    have hck : (k : ℝ) = (m : ℝ) := by rw [← hfl2, hfl]
    rw [hk, hck]
  rw [hy] at h1
  exact lt_irrefl _ h1

/-! ## Isolation of a crossing with non-zero derivative -/

/-- At a crossing of the integer levels in `[0,1)` the function `G` is isolated among the crossings:
the values on the two sides stay strictly inside the adjacent unit intervals. -/
lemma isolated_of_mem (hder : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 → (∃ k : ℤ, G t = (k : ℝ)) →
      HasDerivAt G (deriv G t) t ∧ deriv G t ≠ 0)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) (htc : t ∈ XS G) :
    ∃ δ > 0, ∀ x : ℝ, |x - t| < δ → x ∈ XS G → x = t := by
  obtain ⟨m, hm⟩ := htc
  obtain ⟨hda, hne⟩ := hder t ht ⟨m, hm⟩
  have hdt : HasDerivAt (fun s : ℝ => G (s + t)) (deriv G t) 0 := by
    have h0 : HasDerivAt G (deriv G t) (0 + t) := by simpa using hda
    simpa using HasDerivAt.comp_add_const (f := G) (f' := deriv G t) (0 : ℝ) t h0
  have hmfloor : (m : ℝ) = G t := hm.symm
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · obtain ⟨δ, hδ, h1, h2⟩ := Work.Drive.SCC.floor_of_deriv_neg hdt hneg
    refine ⟨δ, hδ, fun x hx hxc => ?_⟩
    rcases lt_trichotomy x t with hlt | heq | hgt
    · exfalso
      have hxm : x - t ∈ Set.Ioo (-δ) 0 :=
        ⟨by have := (abs_lt.mp hx).1; linarith, by linarith⟩
      have h2' := h2 (x - t) hxm
      rw [show x - t + t = x from by ring] at h2'
      simp only [zero_add] at h2'
      rw [← hmfloor] at h2'
      exact (not_mem_range_of_between (y := G x) h2'.1 h2'.2) hxc
    · exact heq
    · exfalso
      have hxm : x - t ∈ Set.Ioo (0 : ℝ) δ :=
        ⟨by linarith, by have := (abs_lt.mp hx).2; linarith⟩
      have h1' := h1 (x - t) hxm
      rw [show x - t + t = x from by ring] at h1'
      simp only [zero_add] at h1'
      rw [← hmfloor] at h1'
      exact (not_mem_range_of_between (y := G x) (m := m - 1)
        (by push_cast; linarith [h1'.1]) (by push_cast; linarith [h1'.2])) hxc
  · obtain ⟨δ, hδ, h1, h2⟩ := Work.Drive.SCC.floor_of_deriv_pos hdt hpos
    refine ⟨δ, hδ, fun x hx hxc => ?_⟩
    rcases lt_trichotomy x t with hlt | heq | hgt
    · exfalso
      have hxm : x - t ∈ Set.Ioo (-δ) 0 :=
        ⟨by have := (abs_lt.mp hx).1; linarith, by linarith⟩
      have h2' := h2 (x - t) hxm
      rw [show x - t + t = x from by ring] at h2'
      simp only [zero_add] at h2'
      rw [← hmfloor] at h2'
      exact (not_mem_range_of_between (y := G x) (m := m - 1)
        (by push_cast; linarith [h2'.1]) (by push_cast; linarith [h2'.2])) hxc
    · exact heq
    · exfalso
      have hxm : x - t ∈ Set.Ioo (0 : ℝ) δ :=
        ⟨by linarith, by have := (abs_lt.mp hx).2; linarith⟩
      have h1' := h1 (x - t) hxm
      rw [show x - t + t = x from by ring] at h1'
      simp only [zero_add] at h1'
      rw [← hmfloor] at h1'
      exact (not_mem_range_of_between (y := G x) h1'.1 h1'.2) hxc

/-! ## Finiteness of the crossing set in `[0,1)` -/

lemma crossSet_Ico_finite (hcont : Continuous G) (hper : ∀ t : ℝ, G (t + 1) = G t + (n : ℝ))
    (hder : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 → (∃ k : ℤ, G t = (k : ℝ)) →
      HasDerivAt G (deriv G t) t ∧ deriv G t ≠ 0) :
    (Set.Ico (0 : ℝ) 1 ∩ XS G).Finite := by
  have hWclosed : IsClosed (XS G) := by
    have heq : XS G = G ⁻¹' (Set.range (fun k : ℤ => (k : ℝ))) := by
      ext t
      simp only [Set.mem_preimage, Set.mem_range]
      exact ⟨fun ⟨m, hm⟩ => ⟨m, hm.symm⟩, fun ⟨m, hm⟩ => ⟨m, hm.symm⟩⟩
    rw [heq]
    exact Real.isClosed_range_intCast.preimage hcont
  have hKcompact : IsCompact (XS G ∩ Set.Icc (0 : ℝ) 1) :=
    IsCompact.of_isClosed_subset isCompact_Icc (hWclosed.inter isClosed_Icc)
      Set.inter_subset_right
  have hiso : ∀ x ∈ XS G ∩ Set.Icc (0 : ℝ) 1,
      ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ∩ (XS G ∩ Set.Icc (0 : ℝ) 1) ⊆ {x} := by
    rintro x ⟨hxW, hxIcc⟩
    rcases lt_or_eq_of_le hxIcc.2 with hxlt | hxeq
    · obtain ⟨δ, hδ, hδ'⟩ := isolated_of_mem hder ⟨hxIcc.1, hxlt⟩ hxW
      refine ⟨Metric.ball x δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, ?_⟩
      rintro y ⟨hyb, hyW, -⟩
      have hy2 : |y - x| < δ := by
        rw [Metric.mem_ball, Real.dist_eq] at hyb; exact hyb
      exact Set.mem_singleton_iff.mpr (hδ' y hy2 hyW)
    · subst hxeq
      obtain ⟨m1, hm1⟩ := hxW
      have hG0 : G 0 = ((m1 - n : ℤ) : ℝ) := by
        have h := hper 0
        simp only [zero_add] at h
        rw [hm1] at h
        push_cast
        linarith
      have h0W : (0 : ℝ) ∈ XS G := ⟨m1 - n, hG0⟩
      obtain ⟨δ₀, hδ₀, hδ₀'⟩ := isolated_of_mem hder ⟨le_refl 0, by norm_num⟩ h0W
      refine ⟨Metric.ball 1 (min δ₀ 1), Metric.isOpen_ball,
        Metric.mem_ball_self (lt_min hδ₀ one_pos), ?_⟩
      rintro y ⟨hyb, hyW, hyIcc⟩
      have hydist : |y - 1| < min δ₀ 1 := by
        rw [Metric.mem_ball, Real.dist_eq] at hyb; exact hyb
      by_contra hyne
      have hylt : y < 1 := lt_of_le_of_ne hyIcc.2 hyne
      have hsub : |y - 1| < δ₀ := lt_of_lt_of_le hydist (min_le_left _ _)
      have hy1W : y - 1 ∈ XS G := by
        rw [← Work.Drive.SCC.CrossSet_add_one hper (y - 1)]
        simpa using hyW
      have hzero : y - 1 = 0 := hδ₀' (y - 1) (by rwa [sub_zero]) hy1W
      linarith
  have hKfin : (XS G ∩ Set.Icc (0 : ℝ) 1).Finite :=
    Work.Drive.finite_of_isCompact_of_isolated hKcompact hiso
  refine hKfin.subset ?_
  rintro t ⟨htIco, htW⟩
  exact ⟨htW, ⟨htIco.1, le_of_lt htIco.2⟩⟩

/-- There is `δ ∈ (0,1)` which is not a crossing. -/
lemma exists_shift (hfin : (Set.Ico (0 : ℝ) 1 ∩ XS G).Finite) :
    ∃ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) 1 ∧ δ ∉ XS G := by
  have hinf : (Set.Ioo (0 : ℝ) 1).Infinite := Set.Ioo_infinite (by norm_num)
  have hfin' : (Set.Ioo (0 : ℝ) 1 ∩ XS G).Finite :=
    hfin.subset (fun x hx => ⟨⟨le_of_lt hx.1.1, hx.1.2⟩, hx.2⟩)
  obtain ⟨δ, hδ, hδnot⟩ := hinf.exists_notMem_finite hfin'
  exact ⟨δ, hδ, fun hxW => hδnot ⟨hδ, hxW⟩⟩

/-! ## The local jump of `⌊G⌋` at every crossing -/

/-- At every crossing `y ∈ ℝ`, the floor of `G` jumps by `±1` across `y` (the hypothesis needed by
`Work.Surf.floorCrossSet_parity`). -/
lemma hjump_all (hder : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 → (∃ k : ℤ, G t = (k : ℝ)) →
      HasDerivAt G (deriv G t) t ∧ deriv G t ≠ 0)
    (hper : ∀ t : ℝ, G (t + 1) = G t + (n : ℝ)) {y : ℝ} (hy : y ∈ XS G) :
    (∃ ε > 0, (∀ v ∈ Set.Ioo (y - ε) y, ⌊G v⌋ = ⌊G y⌋ - 1) ∧
      (∀ v ∈ Set.Ioo y (y + ε), ⌊G v⌋ = ⌊G y⌋)) ∨
    (∃ ε > 0, (∀ v ∈ Set.Ioo (y - ε) y, ⌊G v⌋ = ⌊G y⌋) ∧
      (∀ v ∈ Set.Ioo y (y + ε), ⌊G v⌋ = ⌊G y⌋ - 1)) := by
  have hyk : Int.fract y + (⌊y⌋ : ℝ) = y := Int.fract_add_floor y
  have hy0mem : Int.fract y ∈ XS G := by
    refine (Work.Drive.SCC.CrossSet_add_intCast hper (Int.fract y) ⌊y⌋).mp ?_
    rwa [hyk]
  have hy0Ico : Int.fract y ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩
  obtain ⟨hda, hne⟩ := hder (Int.fract y) hy0Ico hy0mem
  obtain ⟨m, hm⟩ := hy0mem
  obtain ⟨δ, hδ, h1, h2⟩ := Work.Drive.SCC.floor_near_crossing hm hda hne
  have hfloor_y : ⌊G y⌋ = m + ⌊y⌋ * n := by
    have hfl := floor_G_add_int (G := G) hper (Int.fract y) ⌊y⌋
    rw [hyk] at hfl
    rw [hfl]
    have : ⌊G (Int.fract y)⌋ = m := by rw [hm]; exact Int.floor_intCast m
    rw [this]
  have hLmem : ∀ v : ℝ, v ∈ Set.Ioo (y - δ) y →
      v - (⌊y⌋ : ℝ) ∈ Set.Ioo (Int.fract y - δ) (Int.fract y) := by
    intro v hv
    refine ⟨?_, ?_⟩
    · have h := hv.1; rw [← hyk] at h; linarith
    · have h := hv.2; rw [← hyk] at h; linarith
  have hRmem : ∀ v : ℝ, v ∈ Set.Ioo y (y + δ) →
      v - (⌊y⌋ : ℝ) ∈ Set.Ioo (Int.fract y) (Int.fract y + δ) := by
    intro v hv
    refine ⟨?_, ?_⟩
    · have h := hv.1; rw [← hyk] at h; linarith
    · have h := hv.2; rw [← hyk] at h; linarith
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · right
    refine ⟨δ, hδ, ?_, ?_⟩
    · intro v hv
      rw [← show v - (⌊y⌋ : ℝ) + (⌊y⌋ : ℝ) = v from by ring,
        floor_G_add_int (G := G) hper (v - (⌊y⌋ : ℝ)) ⌊y⌋]
      have hh := h2 (v - (⌊y⌋ : ℝ)) (hLmem v hv)
      rw [if_neg (not_lt.mpr hneg.le)] at hh
      rw [hh, hfloor_y]
    · intro v hv
      rw [← show v - (⌊y⌋ : ℝ) + (⌊y⌋ : ℝ) = v from by ring,
        floor_G_add_int (G := G) hper (v - (⌊y⌋ : ℝ)) ⌊y⌋]
      have hh := h1 (v - (⌊y⌋ : ℝ)) (hRmem v hv)
      rw [if_neg (not_lt.mpr hneg.le)] at hh
      rw [hh, hfloor_y]; ring
  · left
    refine ⟨δ, hδ, ?_, ?_⟩
    · intro v hv
      rw [← show v - (⌊y⌋ : ℝ) + (⌊y⌋ : ℝ) = v from by ring,
        floor_G_add_int (G := G) hper (v - (⌊y⌋ : ℝ)) ⌊y⌋]
      have hh := h2 (v - (⌊y⌋ : ℝ)) (hLmem v hv)
      rw [if_pos hpos] at hh
      rw [hh, hfloor_y]; ring
    · intro v hv
      rw [← show v - (⌊y⌋ : ℝ) + (⌊y⌋ : ℝ) = v from by ring,
        floor_G_add_int (G := G) hper (v - (⌊y⌋ : ℝ)) ⌊y⌋]
      have hh := h1 (v - (⌊y⌋ : ℝ)) (hRmem v hv)
      rw [if_pos hpos] at hh
      rw [hh, hfloor_y]

/-! ## The main theorem -/

/-- **The parity of the crossing count of the integer levels.** Let `G : ℝ → ℝ` be continuous with
`G (t+1) = G t + n` for an integer `n`, and suppose that at every crossing `t ∈ [0,1)` of the integer
levels (`G t ∈ ℤ`) the function `G` is differentiable with non-zero derivative. Then the crossings in
`[0,1)` are finite and their number is congruent to `n` mod 2. -/
theorem ncard_crossSet_mod_two (G : ℝ → ℝ) (hcont : Continuous G) (n : ℤ)
    (hper : ∀ t : ℝ, G (t + 1) = G t + (n : ℝ))
    (hder : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 → (∃ k : ℤ, G t = (k : ℝ)) →
      HasDerivAt G (deriv G t) t ∧ deriv G t ≠ 0) :
    ({t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ k : ℤ, G t = (k : ℝ)}).Finite ∧
      (Set.ncard {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ k : ℤ, G t = (k : ℝ)} : ℤ) ≡ n [ZMOD 2] := by
  classical
  have hfin : (Set.Ico (0 : ℝ) 1 ∩ XS G).Finite := crossSet_Ico_finite hcont hper hder
  have hfinW : (XS G ∩ Set.Ico (0 : ℝ) 1).Finite := by rw [Set.inter_comm]; exact hfin
  have hZeq : {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ k : ℤ, G t = (k : ℝ)}
      = Set.Ico (0 : ℝ) 1 ∩ XS G := by
    ext t
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  obtain ⟨δ, hδIoo, hδnot⟩ := exists_shift hfin
  set F : ℝ → ℝ := fun t => G (t + δ) with hFdef
  have hcontF : Continuous F := hcont.comp (continuous_id.add continuous_const)
  have hperF : ∀ t : ℝ, F (t + 1) = F t + (n : ℝ) := by
    intro t
    simp only [hFdef]
    rw [show t + 1 + δ = (t + δ) + 1 from by ring, hper]
  have hzeroF : ¬ ∃ m : ℤ, F 0 = (m : ℝ) := by
    rintro ⟨m, hm⟩
    exact hδnot ⟨m, by simpa [hFdef] using hm⟩
  -- `1`-periodicity of the crossing set, in the orientation needed below
  have hWper : ∀ t : ℝ, t ∈ XS G ↔ t + 1 ∈ XS G := fun t =>
    (Work.Drive.SCC.CrossSet_add_one hper t).symm
  -- finiteness of the shifted crossing set
  have hWfinIco : (XS G ∩ Set.Ico δ (δ + 1)).Finite := by
    have hIoo : (XS G ∩ Set.Ioo δ (δ + 1)).Finite :=
      Work.Drive.ENPC.finite_inter_Ioo_periodic (XS G) hWper hfinW δ (δ + 1)
    refine hIoo.subset ?_
    rintro t ⟨htW, htIco⟩
    exact ⟨htW, ⟨lt_of_le_of_ne htIco.1 (fun h => hδnot (h ▸ htW)), htIco.2⟩⟩
  have heqsetF : {x : ℝ | x ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ m : ℤ, F x = (m : ℝ)}
      = (fun y : ℝ => y - δ) '' (XS G ∩ Set.Ico δ (δ + 1)) := by
    ext x
    constructor
    · rintro ⟨hxI, hxF⟩
      obtain ⟨m, hm⟩ := hxF
      have hxW : x + δ ∈ XS G := ⟨m, by simpa [hFdef] using hm⟩
      exact ⟨x + δ, ⟨hxW, ⟨by linarith [hxI.1], by linarith [hxI.2]⟩⟩, by ring⟩
    · rintro ⟨y, ⟨hyW, hyI⟩, rfl⟩
      obtain ⟨m, hm⟩ := hyW
      refine ⟨⟨by linarith [hyI.1], by linarith [hyI.2]⟩, ⟨m, ?_⟩⟩
      simp only [hFdef]
      rw [show y - δ + δ = y from by ring, hm]
  have hfinF : {x : ℝ | x ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ m : ℤ, F x = (m : ℝ)}.Finite := by
    rw [heqsetF]
    exact hWfinIco.image _
  -- the local jump condition for the shifted function
  have hjumpF : ∀ x ∈ {x : ℝ | x ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ m : ℤ, F x = (m : ℝ)},
      (∃ ε > 0, (∀ y ∈ Set.Ioo (x - ε) x, ⌊F y⌋ = ⌊F x⌋ - 1) ∧
        (∀ y ∈ Set.Ioo x (x + ε), ⌊F y⌋ = ⌊F x⌋)) ∨
      (∃ ε > 0, (∀ y ∈ Set.Ioo (x - ε) x, ⌊F y⌋ = ⌊F x⌋) ∧
        (∀ y ∈ Set.Ioo x (x + ε), ⌊F y⌋ = ⌊F x⌋ - 1)) := by
    rintro x ⟨hxI, hxF⟩
    obtain ⟨m, hm⟩ := hxF
    have hxW : x + δ ∈ XS G := ⟨m, by simpa [hFdef] using hm⟩
    rcases hjump_all hder hper hxW with ⟨ε, hε, hL, hR⟩ | ⟨ε, hε, hL, hR⟩
    · left
      refine ⟨ε, hε, fun y hy => ?_, fun y hy => ?_⟩
      · have hy' : y + δ ∈ Set.Ioo ((x + δ) - ε) (x + δ) :=
          ⟨by linarith [hy.1], by linarith [hy.2]⟩
        have h := hL (y + δ) hy'
        simpa only [hFdef] using h
      · have hy' : y + δ ∈ Set.Ioo (x + δ) ((x + δ) + ε) :=
          ⟨by linarith [hy.1], by linarith [hy.2]⟩
        have h := hR (y + δ) hy'
        simpa only [hFdef] using h
    · right
      refine ⟨ε, hε, fun y hy => ?_, fun y hy => ?_⟩
      · have hy' : y + δ ∈ Set.Ioo ((x + δ) - ε) (x + δ) :=
          ⟨by linarith [hy.1], by linarith [hy.2]⟩
        have h := hL (y + δ) hy'
        simpa only [hFdef] using h
      · have hy' : y + δ ∈ Set.Ioo (x + δ) ((x + δ) + ε) :=
          ⟨by linarith [hy.1], by linarith [hy.2]⟩
        have h := hR (y + δ) hy'
        simpa only [hFdef] using h
  -- the number of crossings is unchanged by the shift
  have hshift : (XS G ∩ Set.Ico δ (δ + 1)).ncard = (XS G ∩ Set.Ico (0 : ℝ) 1).ncard := by
    have hx0mem : δ - 1 ∈ Set.Ioo (-1 : ℝ) 0 :=
      ⟨by linarith [hδIoo.1], by linarith [hδIoo.2]⟩
    have hx0W : δ - 1 ∉ XS G := by
      intro h
      refine hδnot ?_
      simpa using (Work.Drive.SCC.CrossSet_add_one hper (δ - 1)).mpr h
    have hmain := Work.Drive.ENPC.ncard_shift_periodic hWper hfinW hx0mem hx0W
      (by simpa using hδnot)
    have hmain' : (XS G ∩ Set.Ioo (δ - 1) δ).ncard = (XS G ∩ Set.Ico (0 : ℝ) 1).ncard := by
      simpa using hmain
    have hicoeq : XS G ∩ Set.Ico δ (δ + 1) = XS G ∩ Set.Ioo δ (δ + 1) := by
      ext y
      constructor
      · rintro ⟨hyW, hyI⟩
        exact ⟨hyW, ⟨lt_of_le_of_ne hyI.1 (fun h => hδnot (h ▸ hyW)), hyI.2⟩⟩
      · rintro ⟨hyW, hyI⟩
        exact ⟨hyW, ⟨le_of_lt hyI.1, hyI.2⟩⟩
    have htrans : (XS G ∩ Set.Ioo δ (δ + 1)).ncard = (XS G ∩ Set.Ioo (δ - 1) δ).ncard := by
      have himg : (fun y : ℝ => y + 1) '' (XS G ∩ Set.Ioo (δ - 1) δ)
          = XS G ∩ Set.Ioo δ (δ + 1) := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ⟨(hWper z).mp hz.1, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
        · rintro ⟨hyW, hyI⟩
          refine ⟨y - 1, ⟨?_, ⟨by linarith [hyI.1], by linarith [hyI.2]⟩⟩, by ring⟩
          exact (hWper (y - 1)).mpr (by simpa using hyW)
      rw [← himg, Set.ncard_image_of_injective _ (fun a b h => by linarith)]
    rw [hicoeq, htrans, hmain']
  have hcardF : (Set.ncard {x : ℝ | x ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ m : ℤ, F x = (m : ℝ)})
      = (Set.ncard (XS G ∩ Set.Ico (0 : ℝ) 1)) := by
    rw [heqsetF, Set.ncard_image_of_injective _ (fun a b h => by linarith)]
    exact hshift
  -- the parity
  have hpar := Work.Surf.floorCrossSet_parity F hcontF n hperF hfinF hzeroF hjumpF
  rw [hcardF] at hpar
  have hparZ : Odd (Set.Ico (0 : ℝ) 1 ∩ XS G).ncard ↔ Odd n := by
    rw [Set.inter_comm]; exact hpar
  have hfinGoal : {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ k : ℤ, G t = (k : ℝ)}.Finite := by
    rw [hZeq]; exact hfin
  refine ⟨hfinGoal, ?_⟩
  rw [hZeq]
  rw [modEq_two_iff_odd, odd_natCast]
  exact hparZ

end

end Work.Surf
