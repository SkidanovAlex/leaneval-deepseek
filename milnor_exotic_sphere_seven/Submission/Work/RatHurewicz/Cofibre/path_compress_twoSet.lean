import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RatHurewicz.Cofibre

open scoped unitInterval

/-!
# Compressing a path into one set of a two-set open cover

We prove the "surjectivity half of van Kampen" in path form: for an open cover `X = U ∪ V`
with `U ∩ V` path connected and `V` simply connected in the path sense, every path of `X`
whose endpoints lie in `U` is homotopic relative to its endpoints to a path with image in `U`.

The proof subdivides the unit interval using the Lebesgue number lemma and then replaces each
maximal block of `V`-legs by a path in `U ∩ V`.
-/

/-! ## Sub-paths of a continuous map `ℝ → X` -/

/-- The sub-path of a continuous map `f : ℝ → X` running from the time `a` to the time `b`. -/
noncomputable def pcSeg {X : Type*} [TopologicalSpace X] (f : C(ℝ, X)) (a b : ℝ) :
    Path (f a) (f b) where
  toFun s := f (a + (b - a) * (s : ℝ))
  continuous_toFun := f.continuous.comp (by fun_prop)
  source' := by simp
  target' := by simp

lemma pcSeg_mem {X : Type*} [TopologicalSpace X] {W : Set X} {f : C(ℝ, X)} {a b : ℝ}
    (hab : a ≤ b) (h : ∀ t, a ≤ t → t ≤ b → f t ∈ W) : ∀ s : I, pcSeg f a b s ∈ W := by
  intro s
  show f (a + (b - a) * (s : ℝ)) ∈ W
  refine h _ ?_ ?_
  · nlinarith [s.2.1]
  · nlinarith [s.2.2]

lemma pcSeg_self {X : Type*} [TopologicalSpace X] (f : C(ℝ, X)) (a : ℝ) :
    pcSeg f a a = Path.refl (f a) := by
  ext s
  simp [pcSeg]

/-- Transporting a homotopy of sub-paths along equalities of the parameters. -/
lemma pcCastHomotopicSeg {X : Type*} [TopologicalSpace X] (f : C(ℝ, X)) {a a' b b' : ℝ}
    (ha : a = a') (hb : b = b') {q : Path (f a') (f b')}
    (h : Nonempty (q.Homotopic (pcSeg f a' b'))) :
    Nonempty ((q.cast (congrArg f ha) (congrArg f hb)).Homotopic (pcSeg f a b)) := by
  have hseg : (pcSeg f a' b').cast (congrArg f ha) (congrArg f hb) = pcSeg f a b := by
    ext s
    rw [Path.cast_coe]
    show f (a' + (b' - a') * (s : ℝ)) = f (a + (b - a) * (s : ℝ))
    rw [← ha, ← hb]
  obtain ⟨h'⟩ := h
  exact ⟨hseg ▸ (Path.Homotopic.pathCast h' (congrArg f ha) (congrArg f hb))⟩

/-! ## The reparametrisation rewiring a split path -/

private lemma pcPsi_mem (a m b : ℝ) (hab : a < b) (ham : a ≤ m) (hmb : m ≤ b) (s : I) :
    (m - a) / (b - a) * min (2 * (s : ℝ)) 1 +
      (b - m) / (b - a) * max (2 * (s : ℝ) - 1) 0 ∈ I := by
  have hba : (0 : ℝ) < b - a := by linarith
  have h1 : 0 ≤ (m - a) / (b - a) := div_nonneg (by linarith) (le_of_lt hba)
  have h2 : 0 ≤ (b - m) / (b - a) := div_nonneg (by linarith) (le_of_lt hba)
  constructor
  · have hmin : 0 ≤ min (2 * (s : ℝ)) 1 := le_min (by linarith [s.2.1]) (by norm_num)
    have hmax : 0 ≤ max (2 * (s : ℝ) - 1) 0 := le_max_right _ _
    have e1 := mul_nonneg h1 hmin
    have e2 := mul_nonneg h2 hmax
    linarith
  · have hmin : min (2 * (s : ℝ)) 1 ≤ 1 := min_le_right _ _
    have hmax : max (2 * (s : ℝ) - 1) 0 ≤ 1 := max_le (by linarith [s.2.2]) (by norm_num)
    have e1 : (m - a) / (b - a) * min (2 * (s : ℝ)) 1 ≤ (m - a) / (b - a) * 1 :=
      mul_le_mul_of_nonneg_left hmin h1
    have e2 : (b - m) / (b - a) * max (2 * (s : ℝ) - 1) 0 ≤ (b - m) / (b - a) * 1 :=
      mul_le_mul_of_nonneg_left hmax h2
    have hsum : (m - a) / (b - a) + (b - m) / (b - a) = 1 := by
      field_simp
      ring
    linarith

/-- The piecewise linear reparametrisation exhibiting `(pcSeg a m).trans (pcSeg m b)` as a
reparametrisation of `pcSeg a b`. -/
noncomputable def pcPsi (a m b : ℝ) (hab : a < b) (ham : a ≤ m) (hmb : m ≤ b) : I → I :=
  fun s => ⟨(m - a) / (b - a) * min (2 * (s : ℝ)) 1 +
      (b - m) / (b - a) * max (2 * (s : ℝ) - 1) 0, pcPsi_mem a m b hab ham hmb s⟩

lemma pcPsi_continuous (a m b : ℝ) (hab : a < b) (ham : a ≤ m) (hmb : m ≤ b) :
    Continuous (pcPsi a m b hab ham hmb) := by
  unfold pcPsi
  refine Continuous.subtype_mk ?_ (fun s => pcPsi_mem a m b hab ham hmb s)
  fun_prop

lemma pcPsi_zero (a m b : ℝ) (hab : a < b) (ham : a ≤ m) (hmb : m ≤ b) :
    pcPsi a m b hab ham hmb 0 = 0 := by
  apply Subtype.ext
  show (m - a) / (b - a) * min (2 * (↑(0 : I) : ℝ)) 1 +
      (b - m) / (b - a) * max (2 * (↑(0 : I) : ℝ) - 1) 0 = (↑(0 : I) : ℝ)
  norm_num

lemma pcPsi_one (a m b : ℝ) (hab : a < b) (ham : a ≤ m) (hmb : m ≤ b) :
    pcPsi a m b hab ham hmb 1 = 1 := by
  apply Subtype.ext
  show (m - a) / (b - a) * min (2 * (↑(1 : I) : ℝ)) 1 +
      (b - m) / (b - a) * max (2 * (↑(1 : I) : ℝ) - 1) 0 = (↑(1 : I) : ℝ)
  have hba : (0 : ℝ) < b - a := by linarith
  norm_num
  field_simp
  ring

lemma pcPsi_of_le (a m b : ℝ) (hab : a < b) (ham : a ≤ m) (hmb : m ≤ b) (s : I)
    (hs : (s : ℝ) ≤ 1 / 2) :
    (pcPsi a m b hab ham hmb s : ℝ) = (m - a) / (b - a) * (2 * (s : ℝ)) := by
  show (m - a) / (b - a) * min (2 * (s : ℝ)) 1 +
      (b - m) / (b - a) * max (2 * (s : ℝ) - 1) 0 = _
  rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  ring

lemma pcPsi_of_ge (a m b : ℝ) (hab : a < b) (ham : a ≤ m) (hmb : m ≤ b) (s : I)
    (hs : 1 / 2 ≤ (s : ℝ)) :
    (pcPsi a m b hab ham hmb s : ℝ) =
      (m - a) / (b - a) + (b - m) / (b - a) * (2 * (s : ℝ) - 1) := by
  show (m - a) / (b - a) * min (2 * (s : ℝ)) 1 +
      (b - m) / (b - a) * max (2 * (s : ℝ) - 1) 0 = _
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]
  ring

lemma pcSegTransPcSegEq {X : Type*} [TopologicalSpace X] (f : C(ℝ, X)) {a m b : ℝ}
    (hab : a < b) (ham : a ≤ m) (hmb : m ≤ b) :
    ((pcSeg f a m).trans (pcSeg f m b)) =
      (pcSeg f a b).reparam (pcPsi a m b hab ham hmb) (pcPsi_continuous a m b hab ham hmb)
        (pcPsi_zero a m b hab ham hmb) (pcPsi_one a m b hab ham hmb) := by
  ext s
  rw [Path.trans_apply, Path.coe_reparam]
  simp only [Function.comp_apply]
  have hba : b - a ≠ 0 := by linarith
  split_ifs with hs
  · show f (a + (m - a) * (2 * (s : ℝ))) = f (a + (b - a) * (pcPsi a m b hab ham hmb s : ℝ))
    rw [pcPsi_of_le a m b hab ham hmb s hs]
    congr 1
    field_simp
  · show f (m + (b - m) * (2 * (s : ℝ) - 1)) =
        f (a + (b - a) * (pcPsi a m b hab ham hmb s : ℝ))
    rw [pcPsi_of_ge a m b hab ham hmb s (le_of_lt (not_le.mp hs))]
    congr 1
    field_simp
    ring

lemma pcSegTransPcSegHomotopic {X : Type*} [TopologicalSpace X] (f : C(ℝ, X)) {a m b : ℝ}
    (hab : a < b) (ham : a ≤ m) (hmb : m ≤ b) :
    ((pcSeg f a m).trans (pcSeg f m b)).Homotopic (pcSeg f a b) := by
  rw [pcSegTransPcSegEq f hab ham hmb]
  exact ⟨(Path.Homotopy.reparam (pcSeg f a b) (pcPsi a m b hab ham hmb)
    (pcPsi_continuous a m b hab ham hmb) (pcPsi_zero a m b hab ham hmb)
    (pcPsi_one a m b hab ham hmb)).symm⟩

/-! ## Shifting an `ℕ`-indexed grid -/

/-- The grid obtained from `g` by dropping its first `j` points. -/
abbrev pcGshift (g : ℕ → ℝ) (j : ℕ) : ℕ → ℝ := fun k => g (k + j)

lemma pcGrid_mono {g : ℕ → ℝ} {N : ℕ} (hmono : ∀ k < N, g k < g (k + 1)) :
    ∀ j ≤ N, ∀ i ≤ j, g i ≤ g j := by
  intro j
  induction j with
  | zero =>
    intro _ i hi
    have : i = 0 := Nat.eq_zero_of_le_zero hi
    subst this
    exact le_rfl
  | succ j ih =>
    intro hjN i hij
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact (ih (by omega) i (Nat.lt_succ_iff.mp h)).trans (le_of_lt (hmono j (by omega)))
    · have hie : i = j + 1 := le_antisymm hij h
      rw [hie]

/-- If all legs `0, …, K - 1` of a grid are mapped by `f` into `W`, then so is the whole
interval from `g 0` to `g K`. -/
lemma pcMem_of_legs {X : Type*} [TopologicalSpace X] {W : Set X} {f : C(ℝ, X)} {g : ℕ → ℝ}
    {K : ℕ} (hK : 1 ≤ K) (hmono : ∀ k < K, g k ≤ g (k + 1))
    (hleg : ∀ k < K, ∀ t : ℝ, g k ≤ t → t ≤ g (k + 1) → f t ∈ W) :
    ∀ k ≤ K, ∀ t : ℝ, g 0 ≤ t → t ≤ g k → f t ∈ W := by
  intro k
  induction k with
  | zero =>
    intro _ t h0 hk
    have ht : t = g 0 := le_antisymm hk h0
    subst ht
    exact hleg 0 (by omega) _ le_rfl (hmono 0 (by omega))
  | succ k ih =>
    intro hk t h0 ht
    rcases le_or_gt t (g k) with h | h
    · exact ih (by omega) t h0 h
    · exact hleg k (by omega) t (le_of_lt h) ht

/-! ## The subdivision induction -/

/-- The auxiliary statement: for a continuous `f : ℝ → X` and a grid `g 0 < g 1 < ⋯ < g N`
whose legs are each mapped into `U` or `V`, a path from `f (g 0)` to `f (g N)` with both
endpoints in `U` can be compressed into `U`. -/
def PcAux {X : Type*} [TopologicalSpace X] (U V : Set X) (N : ℕ) : Prop :=
  ∀ (f : C(ℝ, X)) (g : ℕ → ℝ), (∀ k < N, g k < g (k + 1)) →
    ∀ (b : ℕ → Bool), (∀ k < N, ∀ t : ℝ, g k ≤ t → t ≤ g (k + 1) → f t ∈ cond (b k) V U) →
    f (g 0) ∈ U → f (g N) ∈ U →
    ∃ q : Path (f (g 0)) (f (g N)),
      (∀ s, q s ∈ U) ∧ Nonempty (q.Homotopic (pcSeg f (g 0) (g N)))

theorem pcAux_all {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hUV : ∀ a b : ↥(U ∩ V), Nonempty (Path a b))
    (hVsc : ∀ {x y : X} (p q : Path x y), (∀ t, p t ∈ V) → (∀ t, q t ∈ V) →
      Nonempty (Path.Homotopic p q)) :
    ∀ N, PcAux U V N := by
  intro N
  refine Nat.strongRecOn (motive := PcAux U V) N ?_
  intro n ih f g hmono b hleg h0 hN
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    refine ⟨Path.refl (f (g 0)), (fun s => by simpa using h0), ?_⟩
    exact ⟨⟨(Path.Homotopy.refl (Path.refl (f (g 0)))).cast rfl (pcSeg_self f (g 0)).symm⟩⟩
  · by_cases hb0 : b 0 = true
    · -- the first leg is a `V`-leg: peel the whole initial block of `V`-legs
      have hex : ∃ k, 1 ≤ k ∧ k ≤ n ∧ (k = n ∨ b k = false) := ⟨n, by omega, le_rfl, Or.inl rfl⟩
      let j : ℕ := Nat.find hex
      have hjspec : 1 ≤ j ∧ j ≤ n ∧ (j = n ∨ b j = false) := Nat.find_spec hex
      have hjmin : ∀ k < j, ¬ (1 ≤ k ∧ k ≤ n ∧ (k = n ∨ b k = false)) :=
        fun k hk => Nat.find_min hex hk
      have hbV : ∀ k < j, b k = true := by
        intro k hk
        by_contra hc
        rw [Bool.not_eq_true] at hc
        by_cases h0k : k = 0
        · rw [h0k] at hc; rw [hc] at hb0; exact Bool.false_ne_true hb0
        · exact (hjmin k hk) ⟨Nat.pos_of_ne_zero h0k, by omega, Or.inr hc⟩
      have hjN : j ≤ n := hjspec.2.1
      have hcoV : ∀ t, g 0 ≤ t → t ≤ g j → f t ∈ V := by
        have hml := pcMem_of_legs (K := j) hjspec.1 (fun k hk => le_of_lt (hmono k (by omega)))
          (fun k hk t h1 h2 => by
            have hh := hleg k (by omega) t h1 h2
            rwa [hbV k hk] at hh)
        exact fun t h1 h2 => hml j le_rfl t h1 h2
      have hg0V : f (g 0) ∈ V := hcoV (g 0) le_rfl (pcGrid_mono hmono j hjN 0 (by omega))
      have hgjV : f (g j) ∈ V := hcoV (g j) (pcGrid_mono hmono j hjN 0 (by omega)) le_rfl
      have hgjU : f (g j) ∈ U := by
        rcases hjspec.2.2 with h | h
        · rw [h]; exact hN
        · by_cases hlt : j < n
          · have hh := hleg j hlt (g j) le_rfl (le_of_lt (hmono j hlt))
            rwa [h] at hh
          · rw [le_antisymm hjN (by omega)]; exact hN
      obtain ⟨w⟩ := hUV ⟨f (g 0), h0, hg0V⟩ ⟨f (g j), hgjU, hgjV⟩
      have hwU : ∀ s, (w.map continuous_subtype_val) s ∈ U := fun s => (w s).2.1
      have hwV : ∀ s, (w.map continuous_subtype_val) s ∈ V := fun s => (w s).2.2
      have hwHom : Nonempty ((w.map continuous_subtype_val).Homotopic (pcSeg f (g 0) (g j))) :=
        hVsc _ _ hwV (pcSeg_mem (pcGrid_mono hmono j hjN 0 (by omega)) hcoV)
      have hab : g 0 < g n := lt_of_lt_of_le (hmono 0 (by omega))
        (pcGrid_mono hmono n le_rfl 1 (by omega))
      have ham : g 0 ≤ g j := pcGrid_mono hmono j hjN 0 (by omega)
      have hmb : g j ≤ g n := pcGrid_mono hmono n le_rfl j hjN
      have hNJ : (n - j) + j = n := by omega
      have h0'' : f ((pcGshift g j) 0) ∈ U := by
        simpa [pcGshift, Nat.zero_add] using hgjU
      have hN'' : f ((pcGshift g j) (n - j)) ∈ U := by
        simpa [pcGshift, hNJ] using hN
      have hmono'' : ∀ k < n - j, (pcGshift g j) k < (pcGshift g j) (k + 1) := by
        intro k hk
        show g (k + j) < g ((k + 1) + j)
        rw [show (k + 1) + j = (k + j) + 1 by omega]
        exact hmono (k + j) (by omega)
      have hleg'' : ∀ k < n - j, ∀ t : ℝ, (pcGshift g j) k ≤ t → t ≤ (pcGshift g j) (k + 1) →
          f t ∈ cond (b (k + j)) V U := by
        intro k hk t h1 h2
        have h2' : t ≤ g ((k + j) + 1) := by
          rw [show (k + j) + 1 = (k + 1) + j by omega]; exact h2
        exact hleg (k + j) (by omega) t h1 h2'
      obtain ⟨q_tail, hq_img, hq_hom⟩ :=
        ih (n - j) (by omega) f (pcGshift g j) hmono'' (fun k => b (k + j)) hleg'' h0'' hN''
      have haj : g j = (pcGshift g j) 0 := by simp [pcGshift]
      have hbj : g n = (pcGshift g j) (n - j) := by simp [pcGshift, hNJ]
      let qc : Path (f (g j)) (f (g n)) := q_tail.cast (congrArg f haj) (congrArg f hbj)
      have hqc_img : ∀ s, qc s ∈ U := by
        intro s
        simpa [qc, Path.cast_coe] using hq_img s
      have hqc_hom : Nonempty (qc.Homotopic (pcSeg f (g j) (g n))) :=
        pcCastHomotopicSeg f haj hbj hq_hom
      refine ⟨(w.map continuous_subtype_val).trans qc, ?_, ?_⟩
      · intro s
        rw [Path.trans_apply]
        split_ifs with hs
        · exact hwU _
        · exact hqc_img _
      · obtain ⟨hwh⟩ := hwHom
        obtain ⟨hqh⟩ := hqc_hom
        exact ⟨(Path.Homotopic.hcomp hwh hqh).trans
          (pcSegTransPcSegHomotopic f hab ham hmb)⟩
    · -- the first leg is a `U`-leg
      have hb0' : b 0 = false := by
        rw [Bool.not_eq_true] at hb0; exact hb0
      have hab : g 0 < g n := lt_of_lt_of_le (hmono 0 (by omega))
        (pcGrid_mono hmono n le_rfl 1 (by omega))
      have hg01 : g 0 ≤ g 1 := le_of_lt (hmono 0 (by omega))
      have hg1n : g 1 ≤ g n := pcGrid_mono hmono n le_rfl 1 (by omega)
      have hnz : (n - 1) + 1 = n := by omega
      have h0' : f ((pcGshift g 1) 0) ∈ U := by
        have hh := hleg 0 (by omega) (g 1) hg01 le_rfl
        simpa [pcGshift, hb0'] using hh
      have hN' : f ((pcGshift g 1) (n - 1)) ∈ U := by
        simpa [pcGshift, hnz] using hN
      have hmono1 : ∀ k < n - 1, (pcGshift g 1) k < (pcGshift g 1) (k + 1) := by
        intro k hk
        show g (k + 1) < g ((k + 1) + 1)
        exact hmono (k + 1) (by omega)
      have hleg1 : ∀ k < n - 1, ∀ t : ℝ, (pcGshift g 1) k ≤ t → t ≤ (pcGshift g 1) (k + 1) →
          f t ∈ cond (b (k + 1)) V U := by
        intro k hk
        exact hleg (k + 1) (by omega)
      obtain ⟨q_tail, hq_img, hq_hom⟩ :=
        ih (n - 1) (by omega) f (pcGshift g 1) hmono1 (fun k => b (k + 1)) hleg1 h0' hN'
      have ha1 : g 1 = (pcGshift g 1) 0 := by simp [pcGshift]
      have hb1 : g n = (pcGshift g 1) (n - 1) := by simp [pcGshift, hnz]
      let qc : Path (f (g 1)) (f (g n)) := q_tail.cast (congrArg f ha1) (congrArg f hb1)
      have hqc_img : ∀ s, qc s ∈ U := by
        intro s
        simpa [qc, Path.cast_coe] using hq_img s
      have hqc_hom : Nonempty (qc.Homotopic (pcSeg f (g 1) (g n))) :=
        pcCastHomotopicSeg f ha1 hb1 hq_hom
      refine ⟨(pcSeg f (g 0) (g 1)).trans qc, ?_, ?_⟩
      · intro s
        rw [Path.trans_apply]
        split_ifs with hs
        · exact pcSeg_mem hg01 (fun t h1 h2 => by
            have hh := hleg 0 (by omega) t h1 h2
            simpa [hb0'] using hh) _
        · exact hqc_img _
      · obtain ⟨hqh⟩ := hqc_hom
        exact ⟨(Path.Homotopic.hcomp (Path.Homotopic.refl (pcSeg f (g 0) (g 1))) hqh).trans
          (pcSegTransPcSegHomotopic f hab hg01 hg1n)⟩

theorem path_compress_twoSet {X : Type} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hUV : ∀ a b : ↥(U ∩ V), Nonempty (Path a b))
    (hVsc : ∀ {x y : X} (p q : Path x y), (∀ t, p t ∈ V) → (∀ t, q t ∈ V) →
      Nonempty (Path.Homotopic p q))
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (p : Path x y) :
    ∃ q : Path x y, (∀ t, q t ∈ U) ∧ Nonempty (Path.Homotopic p q) := by
  classical
  -- ### Step 1: the Lebesgue number of the pulled-back cover of `I`
  have hcopen : ∀ i : Bool, IsOpen (p ⁻¹' (cond i V U) : Set I) := by
    intro i
    cases i
    · exact hU.preimage p.continuous
    · exact hV.preimage p.continuous
  have hcover : (Set.univ : Set I) ⊆ ⋃ i : Bool, (p ⁻¹' (cond i V U) : Set I) := by
    intro t _
    rcases (show p t ∈ U ∨ p t ∈ V from by
      have := Set.eq_univ_iff_forall.mp hcov (p t)
      simpa [Set.mem_union] using this) with h | h
    · exact Set.mem_iUnion.mpr ⟨false, h⟩
    · exact Set.mem_iUnion.mpr ⟨true, h⟩
  obtain ⟨δ, hδpos, hδ⟩ :=
    lebesgue_number_lemma_of_metric (s := (Set.univ : Set I)) isCompact_univ hcopen hcover
  obtain ⟨mn, hmn⟩ := exists_nat_one_div_lt hδpos
  -- ### Step 2: the uniform grid of mesh `1/N`
  let N : ℕ := mn + 1
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNd : (1 : ℝ) / N < δ := by
    have hcast : ((mn : ℝ) + 1) = (N : ℝ) := by simp [N]
    rw [← hcast]; exact hmn
  let g : ℕ → ℝ := fun k => (k : ℝ) / N
  have hg0 : g 0 = 0 := by simp [g]
  have hgN : g N = 1 := by
    show (N : ℝ) / N = 1
    field_simp
  have hmono : ∀ k < N, g k < g (k + 1) := by
    intro k hk
    show (k : ℝ) / N < ((k + 1 : ℕ) : ℝ) / N
    have h2 : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact div_lt_div_of_pos_right h2 hNR
  -- ### Step 3: classify each leg
  let mid : ∀ k : ℕ, k < N → I := fun k hk => ⟨((k : ℝ) + 1 / 2) / N, by
    have hk1 : k + 1 ≤ N := by omega
    have h1 : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk1
    constructor
    · exact div_nonneg (by positivity) (le_of_lt hNR)
    · rw [div_le_one hNR]; linarith⟩
  let b : ℕ → Bool := fun k =>
    if hk : k < N then Classical.choose (hδ (mid k hk) (Set.mem_univ _)) else false
  have hleg : ∀ k < N, ∀ t : ℝ, g k ≤ t → t ≤ g (k + 1) → p.extend t ∈ cond (b k) V U := by
    intro k hk t ht1 ht2
    have hspec := Classical.choose_spec (hδ (mid k hk) (Set.mem_univ _))
    have hk1 : k + 1 ≤ N := by omega
    have hc1 : (0 : ℝ) ≤ (k : ℝ) / N := by positivity
    have hc2 : ((k + 1 : ℕ) : ℝ) / N ≤ 1 := by
      rw [div_le_one hNR]
      exact_mod_cast hk1
    have htI : t ∈ I :=
      ⟨le_trans (by simpa [g] using hc1) ht1, le_trans ht2 (by simpa [g] using hc2)⟩
    have hball : (⟨t, htI⟩ : I) ∈ Metric.ball (mid k hk) δ := by
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
      have hm1 : (k : ℝ) ≤ N * t := by
        have h1 : (k : ℝ) / N ≤ t := ht1
        rw [div_le_iff₀ hNR] at h1
        linarith
      have hm2 : N * t ≤ (k : ℝ) + 1 := by
        have h2 : t ≤ ((k + 1 : ℕ) : ℝ) / N := ht2
        rw [le_div_iff₀ hNR] at h2
        push_cast at h2
        linarith
      have hkey : |N * t - (k : ℝ) - 1 / 2| ≤ 1 / 2 := by
        rw [abs_le]; constructor <;> linarith
      have heq : t - ((k : ℝ) + 1 / 2) / N = (N * t - (k : ℝ) - 1 / 2) / N := by
        field_simp
        ring
      have hlt : (1 : ℝ) / (2 * N) < δ := by
        have hh : (1 : ℝ) / (2 * N) = (1 / 2) / N := by field_simp
        have hle : (1 : ℝ) / (2 * N) < 1 / N := by
          rw [hh, div_lt_div_iff_of_pos_right hNR]; norm_num
        linarith
      have hkey' : |N * t - (k : ℝ) - 1 / 2| / N ≤ (1 / 2) / N :=
        div_le_div_of_nonneg_right hkey (le_of_lt hNR)
      have hhalf2 : (1 / 2) / N = (1 : ℝ) / (2 * N) := by field_simp
      rw [heq, abs_div, abs_of_pos hNR]
      linarith
    have hmem : p ⟨t, htI⟩ ∈ cond (Classical.choose (hδ (mid k hk) (Set.mem_univ _))) V U :=
      hspec hball
    simpa [b, dif_pos hk, Path.extend_apply p htI] using hmem
  -- ### Step 4: apply the compression induction
  have h0g : p.extend (g 0) ∈ U := by rw [hg0, p.extend_zero]; exact hx
  have hNg : p.extend (g N) ∈ U := by rw [hgN, p.extend_one]; exact hy
  obtain ⟨q, hqU, hqHom⟩ := pcAux_all hUV hVsc N p.extend g hmono b hleg h0g hNg
  have hxg : x = p.extend (g 0) := by rw [hg0, p.extend_zero]
  have hyg : y = p.extend (g N) := by rw [hgN, p.extend_one]
  refine ⟨q.cast hxg hyg, ?_, ?_⟩
  · intro s
    rw [Path.cast_coe]
    exact hqU s
  · obtain ⟨hqh⟩ := hqHom
    have hseg : (pcSeg p.extend (g 0) (g N)).cast hxg hyg = p := by
      ext s
      rw [Path.cast_coe]
      change p.extend (g 0 + (g N - g 0) * (s : ℝ)) = p s
      rw [hg0, hgN]
      simp only [zero_add, sub_zero, one_mul]
      exact (p.extend_apply s.2).trans (congrArg p (Subtype.ext rfl))
    have h2 := Path.Homotopic.pathCast hqh hxg hyg
    rw [hseg] at h2
    exact ⟨h2.symm⟩

end Work.RatHurewicz.Cofibre
