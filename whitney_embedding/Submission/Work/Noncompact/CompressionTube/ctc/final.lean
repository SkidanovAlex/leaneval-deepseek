import Mathlib
import Submission.Work.Noncompact.CompressionTube.collar_defs
import Submission.Work.Noncompact.CompressionTube.ctc.step_core
import Submission.Work.Noncompact.CompressionTube.ctc.exists_transverse_on_Icc
import Submission.Work.Compat.MFDerivCongrV433

/-!
# The two-sided piece family and the global transverse coordinate

This module assembles the target `Work.Noncompact.CompressionTube.collar_transverse_coordinate`:

* `ctc_raw_family` : a `ℤ`-indexed family of global smooth pieces vanishing on the line and
  transverse on the compact windows `[k-3, k+3]` (from `exists_transverse_on_Icc`);
* `ctcFwd` / `ctc_fwd_family` : the *forward* recursion of `ctc_step_exists`, producing pieces
  `Ψ n` (index `n : ℕ`) transverse on `(n - 13/8, n + 2)` with `Ψ (n+1) = Ψ n` on
  `{g ≤ n + 1 - 1/8}`; run twice -- once for `(γ, g)` and once for the reflected data
  `(γ(-·), -g)` (see `transverse_reflect`) -- this gives pieces for every index `k : ℤ`;
* `exists_global_transverse_coordinate` : the cube-root-free assembly, using the integer part
  `⌊g x + 1/4⌋` of the height as the index of the piece used at `x`.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set Function Filter

noncomputable section

set_option maxHeartbeats 1600000

/-! ## The raw family -/

/-- **The raw pieces.**  For every `k : ℤ` a global smooth piece vanishing on the line and
transverse on the window `[k-3, k+3]`. -/
theorem ctc_raw_family {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ) (hinj : Function.Injective γ)
    (hprop : IsProperMap γ) (himm : ∀ s : ℝ, Function.Injective (mfderiv MCreal (MC n) γ s))
    {g : M → ℝ} (hg : ContMDiff (MC n) MCreal smoothOrder g) (hgcore : ∀ s : ℝ, g (γ s) = s) :
    ∃ ψ : ℤ → M → EuclideanSpace ℝ (Fin (n - 1)),
      (∀ k : ℤ, ContMDiff (MC n) (MC (n - 1)) smoothOrder (ψ k)) ∧
      (∀ (k : ℤ) (s : ℝ), ψ k (γ s) = 0) ∧
      (∀ (k : ℤ) (s : ℝ), s ∈ Set.Icc ((k : ℝ) - 3) ((k : ℝ) + 3) →
        Transverse γ g (ψ k) s) := by
  classical
  have h : ∀ k : ℤ, ∃ ψ : M → EuclideanSpace ℝ (Fin (n - 1)),
      ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ ∧ (∀ s : ℝ, ψ (γ s) = 0) ∧
      ∀ s : ℝ, s ∈ Set.Icc ((k : ℝ) - 3) ((k : ℝ) + 3) → Transverse γ g ψ s :=
    fun k => exists_transverse_on_Icc hn hγ hinj hprop himm hg hgcore _ _ (by linarith)
  choose ψ hψc hψ0 hψT using h
  exact ⟨ψ, hψc, hψ0, hψT⟩

/-! ## Reflection -/

set_option maxHeartbeats 400000 in
/-- **Reflection of the data.**  Transversality is invariant under reversing the line and
negating the height function: `t ↦ -t`, `g ↦ -g`. -/
lemma transverse_reflect {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {γ : ℝ → M} {g : M → ℝ}
    (ψ : M → EuclideanSpace ℝ (Fin (n - 1))) (t : ℝ) :
    Transverse (fun u : ℝ => γ (-u)) (-g) ψ t ↔ Transverse γ g ψ (-t) := by
  simp only [Transverse]
  constructor
  · intro h v h1 h2
    refine h v h1 ?_
    rw [mfderiv_neg]
    exact neg_eq_zero.mpr h2
  · intro h v h1 h2
    refine h v h1 ?_
    rw [mfderiv_neg] at h2
    exact neg_eq_zero.mp h2

/-! ## The forward recursion -/

/-- The state of the forward recursion at level `m`: the piece `cur` (with index `m`) which agrees
with the previous piece `prev` on the region `{g ≤ m - 1/8}`. -/
structure FwdState {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    (γ : ℝ → M) (g : M → ℝ) (m : ℕ) where
  prev : M → EuclideanSpace ℝ (Fin (n - 1))
  cur : M → EuclideanSpace ℝ (Fin (n - 1))
  hc : ContMDiff (MC n) (MC (n - 1)) smoothOrder cur
  h0 : ∀ s : ℝ, cur (γ s) = 0
  hT : ∀ s : ℝ, s ∈ Set.Ioo ((m : ℝ) - 13 / 8) ((m : ℝ) + 2) → Transverse γ g cur s
  heq : ∀ x : M, g x ≤ (m : ℝ) - 1 / 8 → cur x = prev x

/-- The forward recursion: from the raw pieces (transverse on `[k-2, k+2]`) build pieces
`Ψ m` (index `m : ℕ`) transverse on `(m - 13/8, m + 2)` with `Ψ (m+1) = Ψ m` on
`{g ≤ m + 1 - 1/8}`. -/
noncomputable def ctcFwd {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ) (hinj : Function.Injective γ)
    (hprop : IsProperMap γ) (himm : ∀ s : ℝ, Function.Injective (mfderiv MCreal (MC n) γ s))
    {g : M → ℝ} (hg : ContMDiff (MC n) MCreal smoothOrder g) (hgcore : ∀ s : ℝ, g (γ s) = s)
    (ψ : ℤ → M → EuclideanSpace ℝ (Fin (n - 1)))
    (hψc : ∀ k : ℤ, ContMDiff (MC n) (MC (n - 1)) smoothOrder (ψ k))
    (hψ0 : ∀ (k : ℤ) (s : ℝ), ψ k (γ s) = 0)
    (hψT : ∀ (k : ℤ) (s : ℝ), s ∈ Set.Icc ((k : ℝ) - 2) ((k : ℝ) + 2) →
      Transverse γ g (ψ k) s) :
    (m : ℕ) → FwdState (n := n) γ g m
  | 0 =>
    { prev := ψ 0
      cur := ψ 0
      hc := hψc 0
      h0 := hψ0 0
      hT := fun s hs => hψT 0 s (by
        refine Set.mem_Icc.mpr ⟨?_, ?_⟩
        · have h := hs.1; simp only [Nat.cast_zero, Int.cast_zero] at h ⊢; linarith
        · have h := hs.2; simp only [Nat.cast_zero, Int.cast_zero] at h ⊢; linarith)
      heq := fun x _ => rfl }
  | (m + 1) => by
    classical
    set st := ctcFwd hn hγ hinj hprop himm hg hgcore ψ hψc hψ0 hψT m with hst
    have hwin : ∀ s : ℝ, s ∈ Set.Ioo (((m + 1 : ℕ) : ℝ) - 21 / 8) (((m + 1 : ℕ) : ℝ) + 1) →
        Transverse γ g st.cur s := by
      intro s hs
      have hs1 : ((m : ℝ) - 13 / 8) < s := by
        have h := hs.1; push_cast at h; linarith
      have hs2 : s < ((m : ℝ) + 2) := by
        have h := hs.2; push_cast at h; linarith
      exact st.hT s (Set.mem_Ioo.mpr ⟨hs1, hs2⟩)
    have hraw : ∀ s : ℝ, s ∈ Set.Icc (((m + 1 : ℕ) : ℝ) - 2) (((m + 1 : ℕ) : ℝ) + 2) →
        Transverse γ g (ψ (((m + 1 : ℕ) : ℤ))) s := by
      intro s hs
      refine hψT (((m + 1 : ℕ) : ℤ)) s (Set.mem_Icc.mpr ⟨?_, ?_⟩)
      · have h := hs.1; push_cast at h ⊢; linarith
      · have h := hs.2; push_cast at h ⊢; linarith
    let hex := ctc_step_exists hn hγ hinj hprop himm hg hgcore (((m + 1 : ℕ) : ℤ)) st.hc
      (hψc (((m + 1 : ℕ) : ℤ))) st.h0 (hψ0 (((m + 1 : ℕ) : ℤ))) hwin hraw
    let Ψ' : M → EuclideanSpace ℝ (Fin (n - 1)) := Classical.choose hex
    let d : ℝ := Classical.choose (Classical.choose_spec hex)
    have hspec : 0 < d ∧ d ≤ 1 / 8 ∧
        ContMDiff (MC n) (MC (n - 1)) smoothOrder Ψ' ∧
        (∀ s : ℝ, Ψ' (γ s) = 0) ∧
        (∀ s : ℝ, s ∈ Set.Ioo ((((m + 1 : ℕ) : ℤ) : ℝ) - 13 / 8)
            ((((m + 1 : ℕ) : ℤ) : ℝ) + 2) → Transverse γ g Ψ' s) ∧
        (∀ x : M, g x ≤ ((((m + 1 : ℕ) : ℤ) : ℝ)) - d → Ψ' x = st.cur x) :=
      Classical.choose_spec (Classical.choose_spec hex)
    refine ⟨st.cur, Ψ', hspec.2.2.1, hspec.2.2.2.1, ?_, ?_⟩
    · intro s hs
      refine hspec.2.2.2.2.1 s ?_
      refine Set.mem_Ioo.mpr ⟨?_, ?_⟩
      · have h := hs.1; push_cast at h ⊢; linarith
      · have h := hs.2; push_cast at h ⊢; linarith
    · intro x hx
      refine hspec.2.2.2.2.2 x ?_
      have h := hx; push_cast at h ⊢
      linarith [hspec.1, hspec.2.1]

/-- **The forward family.** -/
theorem ctc_fwd_family {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ) (hinj : Function.Injective γ)
    (hprop : IsProperMap γ) (himm : ∀ s : ℝ, Function.Injective (mfderiv MCreal (MC n) γ s))
    {g : M → ℝ} (hg : ContMDiff (MC n) MCreal smoothOrder g) (hgcore : ∀ s : ℝ, g (γ s) = s)
    (ψ : ℤ → M → EuclideanSpace ℝ (Fin (n - 1)))
    (hψc : ∀ k : ℤ, ContMDiff (MC n) (MC (n - 1)) smoothOrder (ψ k))
    (hψ0 : ∀ (k : ℤ) (s : ℝ), ψ k (γ s) = 0)
    (hψT : ∀ (k : ℤ) (s : ℝ), s ∈ Set.Icc ((k : ℝ) - 2) ((k : ℝ) + 2) →
      Transverse γ g (ψ k) s) :
    ∃ Ψ : ℕ → M → EuclideanSpace ℝ (Fin (n - 1)),
      (∀ m : ℕ, ContMDiff (MC n) (MC (n - 1)) smoothOrder (Ψ m)) ∧
      (∀ (m : ℕ) (s : ℝ), Ψ m (γ s) = 0) ∧
      (∀ (m : ℕ) (s : ℝ), s ∈ Set.Ioo ((m : ℝ) - 13 / 8) ((m : ℝ) + 2) →
        Transverse γ g (Ψ m) s) ∧
      (∀ (m : ℕ) (x : M), g x ≤ ((m : ℝ) + 1) - 1 / 8 → Ψ (m + 1) x = Ψ m x) ∧
      Ψ 0 = ψ 0 := by
  classical
  have hprev : ∀ m : ℕ, (ctcFwd hn hγ hinj hprop himm hg hgcore ψ hψc hψ0 hψT (m + 1)).prev
      = (ctcFwd hn hγ hinj hprop himm hg hgcore ψ hψc hψ0 hψT m).cur := by
    intro m
    simp only [ctcFwd]
  refine ⟨fun m => (ctcFwd hn hγ hinj hprop himm hg hgcore ψ hψc hψ0 hψT m).cur,
    fun m => (ctcFwd hn hγ hinj hprop himm hg hgcore ψ hψc hψ0 hψT m).hc,
    fun m s => (ctcFwd hn hγ hinj hprop himm hg hgcore ψ hψc hψ0 hψT m).h0 s,
    fun m s hs => (ctcFwd hn hγ hinj hprop himm hg hgcore ψ hψc hψ0 hψT m).hT s (by
      refine Set.mem_Ioo.mpr ⟨?_, ?_⟩
      · have h := hs.1; push_cast at h ⊢; linarith
      · have h := hs.2; push_cast at h ⊢; linarith), ?_, ?_⟩
  · intro m x hx
    have hx' : g x ≤ (((m + 1 : ℕ) : ℝ)) - 1 / 8 := by push_cast at hx ⊢; linarith
    have h := (ctcFwd hn hγ hinj hprop himm hg hgcore ψ hψc hψ0 hψT (m + 1)).heq x hx'
    rw [hprev m] at h
    exact h
  · simp only [ctcFwd]


/-- **The global transverse coordinate.**  The target of the whole chapter. -/
theorem exists_global_transverse_coordinate {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ) (hinj : Function.Injective γ)
    (hprop : IsProperMap γ) (himm : ∀ s : ℝ, Function.Injective (mfderiv MCreal (MC n) γ s))
    {g : M → ℝ} (hg : ContMDiff (MC n) MCreal smoothOrder g) (hgcore : ∀ s : ℝ, g (γ s) = s) :
    ∃ P : M → EuclideanSpace ℝ (Fin (n - 1)), ContMDiff (MC n) (MC (n - 1)) smoothOrder P ∧
      (∀ s : ℝ, P (γ s) = 0) ∧
      ∀ s : ℝ, ∀ v : TangentSpace (MC n) (γ s),
        mfderiv (MC n) (MC (n - 1)) P (γ s) v = 0 →
        mfderiv (MC n) MCreal g (γ s) v = 0 → v = 0 := by
  classical
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  -- (1) the raw family
  obtain ⟨ψ, hψc, hψ0, hψT3⟩ := ctc_raw_family (n := n) hn hγ hinj hprop himm hg hgcore
  have hψT : ∀ (k : ℤ) (s : ℝ), s ∈ Set.Icc ((k : ℝ) - 2) ((k : ℝ) + 2) →
      Transverse γ g (ψ k) s := by
    intro k s hs
    refine hψT3 k s ?_
    rw [Set.mem_Icc] at hs ⊢
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- (2) the forward family for `(γ, g)`
  obtain ⟨Ψf, hΨfc, hΨf0, hΨfT, hΨfe, hΨfb⟩ :=
    ctc_fwd_family (n := n) hn hγ hinj hprop himm hg hgcore ψ hψc hψ0 hψT
  -- (3) the reflected data
  have hγ' : ContMDiff MCreal (MC n) smoothOrder (fun u : ℝ => γ (-u)) :=
    hγ.comp (contMDiff_id (I := MCreal) (n := smoothOrder)).neg
  have hinj' : Function.Injective (fun u : ℝ => γ (-u)) :=
    fun u v huv => neg_injective (hinj huv)
  have hprop' : IsProperMap (fun u : ℝ => γ (-u)) :=
    hprop.comp (Homeomorph.neg ℝ).isProperMap
  have hnegmf : ∀ t : ℝ, mfderiv MCreal MCreal (fun u : ℝ => -u) t
      = -(ContinuousLinearMap.id ℝ (TangentSpace MCreal t)) := by
    intro t
    rw [show (fun u : ℝ => -u) = -(id : ℝ → ℝ) from rfl, mfderiv_neg, mfderiv_id]
  have hinjm : ∀ t : ℝ, Function.Injective (mfderiv MCreal MCreal (fun u : ℝ => -u) t) := by
    intro t a b hab
    have h1 : mfderiv MCreal MCreal (-(fun u : ℝ => u)) t (a - b) = 0 := by
      have key : mfderiv MCreal MCreal (-(fun u : ℝ => u)) t
          = mfderiv MCreal MCreal (fun u : ℝ => -u) t := rfl
      rw [key, map_sub, hab, sub_self]
    rw [mfderiv_neg] at h1
    have h1' : (mfderiv MCreal MCreal (fun u : ℝ => u) t) (a - b) = 0 := neg_eq_zero.mp h1
    have h2 : (-(ContinuousLinearMap.id ℝ (TangentSpace MCreal t))) (a - b) = 0 := by
      have hmid : mfderiv MCreal MCreal (fun u : ℝ => u) t
          = ContinuousLinearMap.id ℝ (TangentSpace MCreal t) := mfderiv_id
      rw [← hmid]
      exact neg_eq_zero.mpr h1'
    have h3 : -((a : TangentSpace MCreal t) - b) = 0 := by
      simpa only [neg_apply, ContinuousLinearMap.id_apply] using h2
    exact sub_eq_zero.mp (neg_eq_zero.mp h3)
  have himm' : ∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) (fun u : ℝ => γ (-u)) t) := by
    intro t
    have hdt : MDifferentiableAt MCreal MCreal (fun u : ℝ => -u) t :=
      (contMDiff_id (I := MCreal) (n := smoothOrder)).neg.mdifferentiableAt hn0
    have hgt : MDifferentiableAt MCreal (MC n) γ (-t) := hγ.mdifferentiableAt hn0
    have hcomp := mfderiv_comp (I := MCreal) (I' := MCreal) (I'' := MC n)
      (f := fun u : ℝ => -u) (g := γ) t hgt hdt
    have hcomp' : mfderiv MCreal (MC n) (fun u : ℝ => γ (-u)) t
        = (mfderiv MCreal (MC n) γ (-t)).comp (mfderiv MCreal MCreal (fun u : ℝ => -u) t) :=
      hcomp
    rw [hcomp']
    intro u v huv
    exact hinjm t (himm (-t) huv)
  have hg' : ContMDiff (MC n) MCreal smoothOrder (-g) := hg.neg
  have hgcore' : ∀ t : ℝ, (-g) ((fun u : ℝ => γ (-u)) t) = t := by
    intro t
    have h := hgcore (-t)
    simp only [Pi.neg_apply]
    linarith
  -- the reflected raw family
  have hψ'c : ∀ k : ℤ, ContMDiff (MC n) (MC (n - 1)) smoothOrder (fun x => ψ (-k) x) :=
    fun k => hψc (-k)
  have hψ'0 : ∀ (k : ℤ) (s : ℝ), (fun x => ψ (-k) x) ((fun u : ℝ => γ (-u)) s) = 0 :=
    fun k s => hψ0 (-k) (-s)
  have hψ'T : ∀ (k : ℤ) (s : ℝ), s ∈ Set.Icc ((k : ℝ) - 2) ((k : ℝ) + 2) →
      Transverse (fun u : ℝ => γ (-u)) (-g) (fun x => ψ (-k) x) s := by
    intro k s hs
    refine (transverse_reflect (γ := γ) (g := g) (ψ := ψ (-k)) s).mpr ?_
    refine hψT (-k) (-s) ?_
    rw [Set.mem_Icc] at hs ⊢
    constructor <;> push_cast <;> linarith [hs.1, hs.2]
  -- (4) the reflected family
  obtain ⟨Ψb, hΨbc, hΨb0, hΨbT, hΨbe, hΨbb⟩ :=
    ctc_fwd_family (n := n) hn hγ' hinj' hprop' himm' hg' hgcore' (fun k => ψ (-k)) hψ'c hψ'0 hψ'T
  have hbase : Ψb 0 = ψ 0 := hΨbb
  -- (5) the merged family
  let Ψ : ℤ → M → EuclideanSpace ℝ (Fin (n - 1)) :=
    fun k => if 0 ≤ k then Ψf k.toNat else Ψb (-k).toNat
  have hcastnn : ∀ k : ℤ, 0 ≤ k → ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
    intro k hk
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hk]
  have hcastneg : ∀ k : ℤ, k ≤ 0 → (((-k).toNat : ℕ) : ℝ) = -(k : ℝ) := by
    intro k hk
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by linarith)]
    simp
  have hΨc : ∀ k : ℤ, ContMDiff (MC n) (MC (n - 1)) smoothOrder (Ψ k) := by
    intro k
    by_cases hk : 0 ≤ k
    · rw [show Ψ k = Ψf k.toNat from by simp only [Ψ, if_pos hk]]
      exact hΨfc k.toNat
    · push_neg at hk
      rw [show Ψ k = Ψb (-k).toNat from by simp only [Ψ, if_neg (not_le.mpr hk)]]
      exact hΨbc (-k).toNat
  have hΨ0 : ∀ (k : ℤ) (s : ℝ), Ψ k (γ s) = 0 := by
    intro k s
    by_cases hk : 0 ≤ k
    · rw [show Ψ k = Ψf k.toNat from by simp only [Ψ, if_pos hk]]
      exact hΨf0 k.toNat s
    · push_neg at hk
      rw [show Ψ k = Ψb (-k).toNat from by simp only [Ψ, if_neg (not_le.mpr hk)]]
      simpa using hΨb0 (-k).toNat (-s)
  have hΨT : ∀ (k : ℤ) (s : ℝ), s ∈ Set.Ioo ((k : ℝ) - 3 / 2) ((k : ℝ) + 13 / 8) →
      Transverse γ g (Ψ k) s := by
    intro k s hs
    by_cases hk : 0 ≤ k
    · rw [show Ψ k = Ψf k.toNat from by simp only [Ψ, if_pos hk]]
      refine hΨfT k.toNat s ?_
      have hc := hcastnn k hk
      rw [Set.mem_Ioo] at hs ⊢
      exact ⟨by linarith [hs.1, hc], by linarith [hs.2, hc]⟩
    · push_neg at hk
      rw [show Ψ k = Ψb (-k).toNat from by simp only [Ψ, if_neg (not_le.mpr hk)]]
      have hc := hcastneg k hk.le
      have hb : Transverse (fun u : ℝ => γ (-u)) (-g) (Ψb (-k).toNat) (-s) := by
        refine hΨbT (-k).toNat (-s) ?_
        rw [Set.mem_Ioo] at hs ⊢
        exact ⟨by linarith [hs.2, hc], by linarith [hs.1, hc]⟩
      have := (transverse_reflect (γ := γ) (g := g) (ψ := Ψb (-k).toNat) (-s)).mp hb
      simpa using this
  have h0eq : Ψ 0 = Ψb 0 := by
    have h1 : Ψ 0 = Ψf 0 := by
      simp only [Ψ, if_pos (le_refl (0 : ℤ))]
      norm_num
    rw [h1, hΨfb, ← hbase]
  have hΨe : ∀ (k : ℤ) (x : M), g x = (k : ℝ) - 1 / 4 → Ψ k =ᶠ[𝓝 x] Ψ (k - 1) := by
    intro k x hx
    by_cases hk : 1 ≤ k
    · -- both pieces come from the forward family
      have hk0 : 0 ≤ k := by linarith
      have hk10 : 0 ≤ k - 1 := by linarith
      have hnat : (k - 1).toNat + 1 = k.toNat := by
        have h1 : (((k - 1).toNat : ℕ) : ℤ) = k - 1 := Int.toNat_of_nonneg hk10
        have h2 : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0
        have h3 : (((k - 1).toNat : ℕ) : ℤ) + 1 = ((k.toNat : ℕ) : ℤ) := by linarith
        exact_mod_cast h3
      rw [show Ψ k = Ψf k.toNat from by simp only [Ψ, if_pos hk0],
        show Ψ (k - 1) = Ψf (k - 1).toNat from by simp only [Ψ, if_pos hk10]]
      have hc1 : (((k - 1).toNat : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [hcastnn (k - 1) hk10]; push_cast; ring
      have hev : ∀ᶠ y in 𝓝 x, g y ≤ (((k - 1).toNat : ℕ) : ℝ) + 1 - 1 / 8 := by
        have hlt : g x < (((k - 1).toNat : ℕ) : ℝ) + 1 - 1 / 8 := by rw [hc1]; linarith
        filter_upwards [((isOpen_lt hg.continuous continuous_const).mem_nhds hlt)] with y hy2
        exact le_of_lt hy2
      filter_upwards [hev] with y hy
      have h1 : Ψf ((k - 1).toNat + 1) y = Ψf ((k - 1).toNat) y := hΨfe (k - 1).toNat y hy
      rwa [hnat] at h1
    · -- the pair comes from the reflected family (with `Ψ 0 = Ψb 0` at the junction)
      push_neg at hk
      have hklt : k < 1 := hk
      have hkle : k ≤ 0 := by linarith
      have hk0 : ¬ (0 ≤ k) ∨ k = 0 := by
        rcases lt_or_eq_of_le hkle with h | h
        · exact Or.inl (not_le.mpr h)
        · exact Or.inr h
      have hnat : (-(k - 1)).toNat = (-k).toNat + 1 := by
        have h5 : (-(k - 1) : ℤ) = -k + 1 := by ring
        have h1 : (((-(k - 1)).toNat : ℕ) : ℤ) = -(k - 1) := Int.toNat_of_nonneg (by linarith)
        have h2 : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by linarith)
        have h3 : (((-(k - 1)).toNat : ℕ) : ℤ) = (((-k).toNat : ℕ) : ℤ) + 1 := by linarith
        exact_mod_cast h3
      have hc2 : (((-k).toNat : ℕ) : ℝ) = -(k : ℝ) := hcastneg k hkle
      have hkcur : Ψ k = Ψb (-k).toNat := by
        rcases hk0 with h0 | h0
        · simp only [Ψ, if_neg h0]
        · subst h0
          rw [h0eq]
          simp
      have hkprev : Ψ (k - 1) = Ψb (-(k - 1)).toNat := by
        have hlt : k - 1 < 0 := by linarith
        simp only [Ψ, if_neg (not_le.mpr hlt)]
      rw [hkcur, hkprev, hnat]
      have hge : ∀ᶠ y in 𝓝 x, -g y ≤ (((-k).toNat : ℕ) : ℝ) + 1 - 1 / 8 := by
        have hlt : -g x < (((-k).toNat : ℕ) : ℝ) + 1 - 1 / 8 := by
          rw [hc2, hx]; ring_nf; norm_num
        filter_upwards [((isOpen_lt (hg.continuous.neg) continuous_const).mem_nhds hlt)] with y hy2
        exact le_of_lt hy2
      filter_upwards [hge] with y hy
      have h1 : Ψb ((-k).toNat + 1) y = Ψb (-k).toNat y := hΨbe (-k).toNat y hy
      exact h1.symm
  -- (6) the assembly: the index used at `x` is `⌊g x + 1/4⌋`
  have hloc : ∀ x₀ : M, (fun x : M => Ψ (⌊g x + 1 / 4⌋) x) =ᶠ[𝓝 x₀] Ψ (⌊g x₀ + 1 / 4⌋) := by
    intro x₀
    set k : ℤ := ⌊g x₀ + 1 / 4⌋ with hk
    have hk1 : (k : ℝ) ≤ g x₀ + 1 / 4 := by rw [hk]; exact Int.floor_le _
    have hk2 : g x₀ + 1 / 4 < (k : ℝ) + 1 := by rw [hk]; exact Int.lt_floor_add_one _
    have hle : (k : ℝ) - 1 / 4 ≤ g x₀ := by linarith
    rcases lt_or_eq_of_le hle with hgt | heq
    · -- the index is locally constant `= k`
      have hopen : IsOpen {y : M | (k : ℝ) < g y + 1 / 4 ∧ g y + 1 / 4 < (k : ℝ) + 1} := by
        refine IsOpen.inter ?_ ?_
        · exact isOpen_lt continuous_const (hg.continuous.add continuous_const)
        · exact isOpen_lt (hg.continuous.add continuous_const) continuous_const
      have hmem : x₀ ∈ {y : M | (k : ℝ) < g y + 1 / 4 ∧ g y + 1 / 4 < (k : ℝ) + 1} :=
        ⟨by linarith, by linarith⟩
      filter_upwards [hopen.mem_nhds hmem] with y hy
      have hfloor : ⌊g y + 1 / 4⌋ = k := by
        rw [hk, Int.floor_eq_iff]
        exact ⟨le_of_lt hy.1, hy.2⟩
      rw [hfloor]
    · -- the index meets the jump at `g x₀ = k - 1/4`; the two pieces agree there
      have hev : Ψ k =ᶠ[𝓝 x₀] Ψ (k - 1) := hΨe k x₀ heq.symm
      have hopen : IsOpen {y : M | (k : ℝ) - 1 < g y + 1 / 4 ∧ g y + 1 / 4 < (k : ℝ) + 1} := by
        refine IsOpen.inter ?_ ?_
        · exact isOpen_lt continuous_const (hg.continuous.add continuous_const)
        · exact isOpen_lt (hg.continuous.add continuous_const) continuous_const
      have hmem : x₀ ∈ {y : M | (k : ℝ) - 1 < g y + 1 / 4 ∧ g y + 1 / 4 < (k : ℝ) + 1} :=
        ⟨by rw [← heq]; linarith, by linarith⟩
      filter_upwards [hopen.mem_nhds hmem, hev] with y hy hyev
      have hlow : (k : ℤ) - 1 ≤ ⌊g y + 1 / 4⌋ := by
        by_contra hcon
        push_neg at hcon
        have h3 : ⌊g y + 1 / 4⌋ ≤ k - 2 := by omega
        have h4 := (Int.floor_le_iff (z := k - 2) (a := g y + 1 / 4)).mp h3
        push_cast at h4
        linarith [hy.1]
      have hupp : ⌊g y + 1 / 4⌋ ≤ k :=
        (Int.floor_le_iff (z := k) (a := g y + 1 / 4)).mpr hy.2
      have hfloor : ⌊g y + 1 / 4⌋ = k ∨ ⌊g y + 1 / 4⌋ = k - 1 := by omega
      rcases hfloor with hf | hf
      · rw [hf]
      · rw [hf, hyev]
  have hone : ∀ s : ℝ, ⌊g (γ s) + 1 / 4⌋ = ⌊s + 1 / 4⌋ := by
    intro s
    rw [hgcore s]
  refine ⟨fun x => Ψ (⌊g x + 1 / 4⌋) x, ?_, ?_, ?_⟩
  · intro x₀
    refine ((hΨc ⌊g x₀ + 1 / 4⌋).contMDiffAt).congr_of_eventuallyEq ?_
    exact hloc x₀
  · intro s
    simpa only [hone s] using hΨ0 ⌊s + 1 / 4⌋ s
  · intro s v hPv hgv
    have hder : mfderiv (MC n) (MC (n - 1)) (fun x : M => Ψ ⌊g x + 1 / 4⌋ x) (γ s)
        = mfderiv (MC n) (MC (n - 1)) (Ψ ⌊s + 1 / 4⌋) (γ s) := by
      have h := Filter.EventuallyEq.mfderiv_eq_v433 (I := MC n) (I' := MC (n - 1)) (hloc (γ s))
      rwa [hone s] at h
    have hfl1 : ((⌊s + 1 / 4⌋ : ℤ) : ℝ) ≤ s + 1 / 4 := Int.floor_le _
    have hfl2 : s + 1 / 4 < ((⌊s + 1 / 4⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hgt : mfderiv (MC n) (MC (n - 1)) (Ψ ⌊s + 1 / 4⌋) (γ s) v = 0 := by
      rw [← hder]
      exact hPv
    refine hΨT ⌊s + 1 / 4⌋ s (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩) v hgt hgv

end

end Work.Noncompact.CompressionTube
