import Mathlib

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

noncomputable section

namespace Work.EKLRelCross

/-!
# The abstract cross-section construction (Pisa §6.9–6.12)

This file records the abstract "greedy/Borel transversal" construction used to build the local
cross-section of `pisa_crosssection`.  Everything here is about a group acting continuously on a
metric space; nothing specific to `SL₃(ℝ)` or `X₃` is used.

The central notion is the *lexicographic minimum* of a compact set with respect to the order
induced by the distances to a fixed dense sequence `d : ℕ → Y`.
-/

/-- `x` is the lexicographic minimum of `K` with respect to the order induced by the distances to
the sequence `d`: no `y ∈ K` agrees with `x` on the earlier distances and beats it at a later one. -/
def IsLexMin {Y : Type*} [PseudoMetricSpace Y] (d : ℕ → Y) (K : Set Y) (x : Y) : Prop :=
  x ∈ K ∧ ∀ y ∈ K, ∀ N : ℕ, (∀ n < N, dist y (d n) = dist x (d n)) → dist x (d N) ≤ dist y (d N)

/-- Two points of a metric space with equal distances to all terms of a dense sequence are equal. -/
theorem eq_of_forall_dist_dense {Y : Type*} [MetricSpace Y] {d : ℕ → Y} (hd : DenseRange d)
    {x y : Y} (h : ∀ n, dist x (d n) = dist y (d n)) : x = y := by
  have hlt : ∀ ε : ℝ, 0 < ε → dist x y < ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := (Metric.denseRange_iff.mp hd) y (ε / 2) (by linarith)
    have h1 : dist x (d n) = dist y (d n) := h n
    have h2 : dist x y ≤ dist x (d n) + dist (d n) y := dist_triangle _ _ _
    rw [h1, dist_comm (d n) y] at h2
    linarith
  have h0 : dist x y = 0 := by
    by_contra hne
    have hpos : 0 < dist x y := by
      rw [dist_pos]
      intro hxy
      exact hne (by rw [hxy, dist_self])
    linarith [hlt (dist x y / 2) (by linarith)]
  exact eq_of_dist_eq_zero h0

/-- **Lexicographic minima of compact sets.**  For a dense sequence `d` in a metric space and a
nonempty compact set `K`, the lexicographic minimum of `K` exists and is unique. -/
theorem isLexMin_exists_unique {Y : Type*} [MetricSpace Y] (d : ℕ → Y) (hd : DenseRange d)
    {K : Set Y} (hK : IsCompact K) (hne : K.Nonempty) : ∃! x : Y, IsLexMin d K x := by
  classical
  let Kf : ℕ → Set Y := fun n =>
    Nat.rec K (fun m K' => K' ∩ {x | dist x (d m) = sInf (dist (d m) '' K')}) n
  have hzero : Kf 0 = K := rfl
  have hsucc : ∀ n, Kf (n + 1) = Kf n ∩ {x | dist x (d n) = sInf (dist (d n) '' Kf n)} :=
    fun n => rfl
  have hsub : ∀ n, Kf n ⊆ K := by
    intro n
    induction n with
    | zero => exact subset_rfl
    | succ n ih => rw [hsucc n]; exact Set.inter_subset_left.trans ih
  have hclosed : ∀ n, IsClosed (Kf n) := by
    intro n
    induction n with
    | zero => rw [hzero]; exact hK.isClosed
    | succ n ih =>
      rw [hsucc n]
      exact ih.inter (isClosed_eq (continuous_id.dist continuous_const) continuous_const)
  have hcomp : ∀ n, IsCompact (Kf n) := fun n => hK.of_isClosed_subset (hclosed n) (hsub n)
  have hne' : ∀ n, (Kf n).Nonempty := by
    intro n
    induction n with
    | zero => rw [hzero]; exact hne
    | succ n ih =>
      obtain ⟨x, hx⟩ := ih
      have himg : IsCompact (dist (d n) '' Kf n) :=
        (hcomp n).image (continuous_const.dist continuous_id)
      have himgne : (dist (d n) '' Kf n).Nonempty := ⟨dist (d n) x, x, hx, rfl⟩
      have hmem : sInf (dist (d n) '' Kf n) ∈ dist (d n) '' Kf n :=
        himg.sInf_mem himgne
      obtain ⟨y, hy, hyeq⟩ := hmem
      refine ⟨y, ?_⟩
      rw [hsucc n]
      refine ⟨hy, ?_⟩
      show dist y (d n) = sInf (dist (d n) '' Kf n)
      rw [dist_comm]
      exact hyeq
  have hanti : ∀ n, Kf (n + 1) ⊆ Kf n := fun n => by rw [hsucc n]; exact Set.inter_subset_left
  obtain ⟨x0, hx0⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed Kf hanti
    hne' (hcomp 0) hclosed
  have hx0mem : ∀ n, x0 ∈ Kf n := fun n => Set.mem_iInter.mp hx0 n
  have hx0K : x0 ∈ K := by rw [← hzero]; exact hx0mem 0
  have hsame : ∀ x ∈ ⋂ n, Kf n, ∀ y ∈ ⋂ n, Kf n, x = y := by
    intro x hx y hy
    refine eq_of_forall_dist_dense hd fun n => ?_
    have hx1 : x ∈ Kf (n + 1) := Set.mem_iInter.mp hx (n + 1)
    have hy1 : y ∈ Kf (n + 1) := Set.mem_iInter.mp hy (n + 1)
    rw [hsucc n] at hx1 hy1
    exact hx1.2.trans hy1.2.symm
  have hlexmin : ∀ y ∈ K, ∀ N : ℕ,
      (∀ n < N, dist y (d n) = dist x0 (d n)) → dist x0 (d N) ≤ dist y (d N) := by
    intro y hy N hagree
    have hmem : ∀ n ≤ N, y ∈ Kf n := by
      intro n hn
      induction n with
      | zero => rw [hzero]; exact hy
      | succ n ih =>
        have hyK : y ∈ Kf n := ih (Nat.le_of_succ_le hn)
        have hx1 : x0 ∈ Kf (n + 1) := hx0mem (n + 1)
        rw [hsucc n] at hx1
        have : dist y (d n) = sInf (dist (d n) '' Kf n) := by
          rw [← hx1.2]
          exact hagree n (Nat.lt_of_succ_le hn)
        rw [hsucc n]
        exact ⟨hyK, this⟩
    have hyN : y ∈ Kf N := hmem N le_rfl
    have hx1 : x0 ∈ Kf (N + 1) := hx0mem (N + 1)
    rw [hsucc N] at hx1
    calc dist x0 (d N) = sInf (dist (d N) '' Kf N) := hx1.2
      _ ≤ dist y (d N) := csInf_le ((hcomp N).image (continuous_const.dist continuous_id)).bddBelow
        (show dist y (d N) ∈ dist (d N) '' Kf N from ⟨y, hyN, dist_comm _ _⟩)
  refine ⟨x0, ⟨hx0K, hlexmin⟩, ?_⟩
  intro x hx
  by_contra hxy
  have hex : ∃ N, dist x (d N) ≠ dist x0 (d N) := by
    by_contra h
    push_neg at h
    exact hxy (eq_of_forall_dist_dense hd h)
  set N := Nat.find hex with hN
  have hNmin : ∀ n < N, dist x0 (d n) = dist x (d n) := fun n hn =>
    (not_not.mp (Nat.find_min hex hn)).symm
  have hNne : dist x (d N) ≠ dist x0 (d N) := Nat.find_spec hex
  rcases lt_or_gt_of_ne hNne with hlt | hgt
  · exact absurd (hlexmin x hx.1 N (fun n hn => (hNmin n hn).symm)) (not_le.mpr hlt)
  · exact absurd (hx.2 x0 hx0K N hNmin) (not_le.mpr hgt)

/-- **Borel measurability of the lexicographic-minimum set.**  For a compact relation
`R ⊆ Y × Y`, the set of points `x` that are the lexicographic minimum of their own section is
Borel. -/
theorem isLexMin_set_measurable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (d : ℕ → Y) (hd : DenseRange d) {R : Set (Y × Y)} (hR : IsCompact R) :
    MeasurableSet {x : Y | IsLexMin d {y | (x, y) ∈ R} x} := by
  classical
  let S : ℕ → ℚ → Set (Y × Y) := fun N s =>
    R ∩ {p : Y × Y | (∀ n < N, dist p.2 (d n) = dist p.1 (d n)) ∧
      dist p.2 (d N) ≤ dist p.1 (d N) - (s : ℝ)}
  have hSclosed : ∀ N s, IsClosed (S N s) := by
    intro N s
    have h1 : IsClosed {p : Y × Y | ∀ n < N, dist p.2 (d n) = dist p.1 (d n)} := by
      have hset : {p : Y × Y | ∀ n < N, dist p.2 (d n) = dist p.1 (d n)} =
          ⋂ (n : {m : ℕ // m < N}), {p : Y × Y | dist p.2 (d n.1) = dist p.1 (d n.1)} := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_iInter, Subtype.forall]
      rw [hset]
      exact isClosed_iInter fun n => isClosed_eq (continuous_snd.dist continuous_const)
        (continuous_fst.dist continuous_const)
    have h2 : IsClosed {p : Y × Y | dist p.2 (d N) ≤ dist p.1 (d N) - (s : ℝ)} :=
      isClosed_le (continuous_snd.dist continuous_const)
        ((continuous_fst.dist continuous_const).sub continuous_const)
    have hS : S N s = R ∩ ({p : Y × Y | ∀ n < N, dist p.2 (d n) = dist p.1 (d n)} ∩
        {p : Y × Y | dist p.2 (d N) ≤ dist p.1 (d N) - (s : ℝ)}) := by
      rw [show S N s = R ∩ {p : Y × Y | (∀ n < N, dist p.2 (d n) = dist p.1 (d n)) ∧
          dist p.2 (d N) ≤ dist p.1 (d N) - (s : ℝ)} from rfl]
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [hS]
    exact hR.isClosed.inter (h1.inter h2)
  have hScomp : ∀ N s, IsCompact (S N s) := fun N s => hR.of_isClosed_subset (hSclosed N s)
    Set.inter_subset_left
  have hbad : ∀ N : ℕ, MeasurableSet {x : Y | ∃ y : Y, (x, y) ∈ R ∧
      (∀ n < N, dist y (d n) = dist x (d n)) ∧ dist y (d N) < dist x (d N)} := by
    intro N
    have hset : {x : Y | ∃ y : Y, (x, y) ∈ R ∧
        (∀ n < N, dist y (d n) = dist x (d n)) ∧ dist y (d N) < dist x (d N)} =
        ⋃ (s : {q : ℚ // 0 < q}), Prod.fst '' S N (s : ℚ) := by
      ext x
      constructor
      · rintro ⟨y, hxy, heq, hlt⟩
        obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn
          (show (0 : ℝ) < dist x (d N) - dist y (d N) by linarith)
        have ht0 : (0 : ℚ) < t := by exact_mod_cast ht1
        refine Set.mem_iUnion.mpr ⟨⟨t, ht0⟩, (x, y), ⟨hxy, heq, ?_⟩, rfl⟩
        linarith
      · intro hx
        obtain ⟨s, p, hp, hp1⟩ := Set.mem_iUnion.mp hx
        refine ⟨p.2, by rw [← hp1]; exact hp.1, by rw [← hp1]; exact hp.2.1, ?_⟩
        have hs : (0 : ℝ) < (s : ℚ) := by exact_mod_cast s.2
        have := hp.2.2
        rw [hp1] at this
        linarith
    rw [hset]
    exact MeasurableSet.iUnion fun s => ((hScomp N (s : ℚ)).image continuous_fst).measurableSet
  have hdiag : MeasurableSet {x : Y | (x, x) ∈ R} :=
    (hR.isClosed.preimage (continuous_id.prodMk continuous_id)).measurableSet
  have hmain : {x : Y | IsLexMin d {y | (x, y) ∈ R} x} =
      {x : Y | (x, x) ∈ R} ∩ ⋂ N, {x : Y | ∃ y : Y, (x, y) ∈ R ∧
        (∀ n < N, dist y (d n) = dist x (d n)) ∧ dist y (d N) < dist x (d N)}ᶜ := by
    ext x
    simp only [IsLexMin, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
      not_exists, not_and]
    constructor
    · rintro ⟨hxR, hmin⟩
      exact ⟨hxR, fun N y hy hyeq hlt => absurd (hmin y hy N hyeq) (not_le.mpr hlt)⟩
    · rintro ⟨hxR, hbad'⟩
      refine ⟨hxR, fun y hy N hyeq => ?_⟩
      by_contra hcon
      exact hbad' N y hy hyeq (not_le.mp hcon)
  rw [hmain]
  exact hdiag.inter (MeasurableSet.iInter fun N => (hbad N).compl)

/-- **The abstract cross-section (Pisa §6.9–6.12).**  Let a group `G` act continuously on a metric
space `X`, let `B ⊆ A` be compact subsets of `G` with `1 ∈ B`, `B⁻¹ ⊆ A`, `B·B ⊆ A` and
`B·B⁻¹ ⊆ A`, and let `E ⊆ X` be compact.  Assume that any two elements of `A` moving points of
`E` to one and the same point differ (on both sides) by an element of `B`, and that the orbit map
at every point of `E` is injective on `B`.  Then there is a Borel set `C ⊆ E` meeting every
`B`-orbit of a point of `E` exactly once.

The proof is the "greedy" construction of Einsiedler–Lindenstrauss (Pisa Prop. 6.7 with
§6.9–6.12), realised here through lexicographic minima: `C` is the set of points of `E` that are
the lexicographic minimum of their own section of the relation
`R = {(x,y) | x ∈ E, y ∈ E, ∃ b ∈ B, y = b • x}`. -/
theorem exists_borel_crossSection {X G : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [Group G] [TopologicalSpace G] [MulAction G X]
    [ContinuousSMul G X] (B A : Set G) (E : Set X) (hEc : IsCompact E) (d : ℕ → X)
    (hd : DenseRange d) (hBc : IsCompact B) (hAc : IsCompact A) (h1B : (1 : G) ∈ B)
    (hBA : B ⊆ A) (hBinv : ∀ g ∈ B, g⁻¹ ∈ A)
    (hBB : ∀ g ∈ B, ∀ g' ∈ B, g * g' ∈ A)
    (hBBinv : ∀ g ∈ B, ∀ g' ∈ B, g * g'⁻¹ ∈ A)
    (hshrink : ∀ x ∈ E, ∀ x' ∈ E, ∀ u ∈ A, ∀ u' ∈ A,
      u • x = u' • x' → u' * u⁻¹ ∈ B ∧ u⁻¹ * u' ∈ B)
    (hinj : ∀ x ∈ E, ∀ u ∈ B, ∀ u' ∈ B, u • x = u' • x → u = u') :
    ∃ C : Set X, C ⊆ E ∧ MeasurableSet C ∧ ∀ x ∈ E, ∃! t : G, t ∈ B ∧ t • x ∈ C := by
  classical
  have h1A : (1 : G) ∈ A := hBA h1B
  set Rb : Set (X × X) := {p | p.1 ∈ E ∧ p.2 ∈ E ∧ ∃ b ∈ B, p.2 = b • p.1} with hRb
  have hRcomp : IsCompact Rb := by
    have himg : IsCompact ((fun p : G × X => (p.2, p.1 • p.2)) '' (B ×ˢ E)) :=
      (hBc.prod hEc).image (continuous_snd.prodMk continuous_smul)
    have hE2 : IsClosed (E ×ˢ E) := hEc.isClosed.prod hEc.isClosed
    have hset : Rb = ((fun p : G × X => (p.2, p.1 • p.2)) '' (B ×ˢ E)) ∩ (E ×ˢ E) := by
      rw [hRb]
      ext p
      constructor
      · rintro ⟨h1, h2, b, hb, hb2⟩
        refine ⟨⟨(b, p.1), ⟨hb, h1⟩, ?_⟩, h1, h2⟩
        show ((fun p : G × X => (p.2, p.1 • p.2)) (b, p.1)) = p
        rw [Prod.ext_iff]
        exact ⟨rfl, hb2.symm⟩
      · rintro ⟨⟨q, hq, hqe⟩, h1, h2⟩
        obtain ⟨hb, hx⟩ := hq
        have hfst : p.1 = q.2 := by rw [← hqe]
        have hsnd : p.2 = q.1 • q.2 := by rw [← hqe]
        exact ⟨by rw [hfst]; exact hx, h2, q.1, hb, by rw [hsnd, hfst]⟩
    rw [hset]
    exact himg.of_isClosed_subset (himg.isClosed.inter hE2) Set.inter_subset_left
  have hsec_sub : ∀ x : X, {y : X | (x, y) ∈ Rb} ⊆ E := by
    intro x y hy
    rw [hRb] at hy
    exact hy.2.1
  have hsec_comp : ∀ x : X, IsCompact {y : X | (x, y) ∈ Rb} := by
    intro x
    refine hEc.of_isClosed_subset ?_ (hsec_sub x)
    exact hRcomp.isClosed.preimage (continuous_const.prodMk continuous_id)
  have hsec_ne : ∀ x ∈ E, ({y : X | (x, y) ∈ Rb}).Nonempty := by
    intro x hx
    exact ⟨x, by rw [hRb]; exact ⟨hx, hx, 1, h1B, (one_smul G x).symm⟩⟩
  have hclass : ∀ x ∈ E, ∀ y ∈ E, y ∈ {y : X | (x, y) ∈ Rb} →
      {y' : X | (y, y') ∈ Rb} = {y' : X | (x, y') ∈ Rb} := by
    intro x hx y hy hysec
    rw [hRb] at hysec
    obtain ⟨-, -, b, hb, hby⟩ := hysec
    ext z
    constructor
    · intro hz
      have hzE : z ∈ E := hsec_sub y hz
      rw [hRb] at hz
      obtain ⟨-, hzE', b', hb', hbz⟩ := hz
      have hbz' : z = b' • y := hbz
      have hby' : y = b • x := hby
      have hz' : z = (b' * b) • x := by rw [hbz', hby', mul_smul]
      have hmem : b' * b ∈ A := hBB b' hb' b hb
      have hgen := hshrink z hzE x hx (1 : G) h1A (b' * b) hmem (by rw [one_smul, hz'])
      have hBmem : b' * b ∈ B := by simpa using hgen.1
      rw [hRb]
      exact ⟨hx, hzE, b' * b, hBmem, hz'⟩
    · intro hz
      have hzE : z ∈ E := hsec_sub x hz
      rw [hRb] at hz
      obtain ⟨-, -, b'', hb'', hbz⟩ := hz
      have hbz' : z = b'' • x := hbz
      have hby' : y = b • x := hby
      have hz' : z = (b'' * b⁻¹) • y := by rw [hbz', hby', mul_smul, inv_smul_smul]
      have hmem : b'' * b⁻¹ ∈ A := hBBinv b'' hb'' b hb
      have hgen := hshrink z hzE y hy (1 : G) h1A (b'' * b⁻¹) hmem (by rw [one_smul, hz'])
      have hBmem : b'' * b⁻¹ ∈ B := by simpa using hgen.1
      rw [hRb]
      exact ⟨hy, hzE, b'' * b⁻¹, hBmem, hz'⟩
  set C : Set X := {x : X | IsLexMin d {y : X | (x, y) ∈ Rb} x} with hC
  have hCmeas : MeasurableSet C := by
    rw [hC]
    exact isLexMin_set_measurable d hd hRcomp
  have hCsub : C ⊆ E := by
    intro x hx
    rw [hC] at hx
    exact hsec_sub x hx.1
  refine ⟨C, hCsub, hCmeas, ?_⟩
  intro x hx
  obtain ⟨c, hc, huniq⟩ := isLexMin_exists_unique d hd (hsec_comp x) (hsec_ne x hx)
  have hcE : c ∈ E := hsec_sub x hc.1
  have hcC : c ∈ C := by
    rw [hC]
    show IsLexMin d {y : X | (c, y) ∈ Rb} c
    rw [hclass x hx c hcE hc.1]
    exact hc
  have hcex : ∃ b ∈ B, c = b • x := by
    rw [hRb] at hc
    exact hc.1.2.2
  obtain ⟨b, hb, hbc⟩ := hcex
  refine ⟨b, ⟨hb, ?_⟩, ?_⟩
  · rw [← hbc]; exact hcC
  · intro t ht
    obtain ⟨htB, htcC⟩ := ht
    have htcE : t • x ∈ E := hCsub htcC
    have htsec : t • x ∈ {y : X | (x, y) ∈ Rb} := by
      rw [hRb]
      exact ⟨hx, htcE, t, htB, rfl⟩
    have hkey : IsLexMin d {y : X | (x, y) ∈ Rb} (t • x) := by
      rw [hC] at htcC
      have hcc : IsLexMin d {y : X | (t • x, y) ∈ Rb} (t • x) := htcC
      rw [hclass x hx (t • x) htcE htsec] at hcc
      exact hcc
    exact (hinj x hx b hb t htB (by rw [← hbc, huniq (t • x) hkey])).symm

end Work.EKLRelCross
