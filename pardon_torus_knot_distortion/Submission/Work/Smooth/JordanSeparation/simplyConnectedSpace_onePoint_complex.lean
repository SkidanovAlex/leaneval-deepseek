import Mathlib
import Submission.Work.Smooth.SphereJordan.mobiusAddInv
import Submission.Work.Smooth.JordanSeparation.onePoint_locallyPathConnected

/-!
# The Riemann sphere `OnePoint ℂ` is simply connected

The Riemann sphere `OnePoint ℂ = ℂ ∪ {∞}` is homeomorphic to the `2`-sphere, hence simply
connected.  The proof below is the elementary van Kampen argument for the cover of
`OnePoint ℂ` by the two charts `X \ {p}` (`p` a finite point); it uses:

* a Lebesgue-number subdivision of a loop (`exists_monotone_Icc_subset_open_cover_unitInterval`),
* a *spoke* to the base point in each successive intersection of the labels
  (`loop_nullhomotopic_of_cover`), and
* the simple connectivity of each chart: `X \ {∞} ≅ ℂ` is contractible, and `X \ {p}` for
  `p ∈ ℂ` is the image of `X \ {∞}` under the inversion homeomorphism
  `Work.Smooth.SphereJordan.invHomeomorph` of the Riemann sphere, followed by a translation.

## Main result

* `simplyConnectedSpace_onePoint_complex : SimplyConnectedSpace (OnePoint ℂ)`.
-/

open Set

namespace Path

variable {X : Type*} [TopologicalSpace X]

/-- The affine parametrization of the subinterval `[a,b]` of the unit interval. -/
def affine (a b : unitInterval) (s : unitInterval) : unitInterval :=
  ⟨(a : ℝ) + ((b : ℝ) - (a : ℝ)) * (s : ℝ), by
    have ha0 : (0 : ℝ) ≤ a := a.2.1
    have ha1 : (a : ℝ) ≤ 1 := a.2.2
    have hb0 : (0 : ℝ) ≤ b := b.2.1
    have hb1 : (b : ℝ) ≤ 1 := b.2.2
    have hs0 : (0 : ℝ) ≤ s := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have key : (a : ℝ) + ((b : ℝ) - (a : ℝ)) * (s : ℝ)
        = (1 - (s : ℝ)) * (a : ℝ) + (s : ℝ) * (b : ℝ) := by ring
    rw [key]
    constructor
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - s) ha0, mul_nonneg hs0 hb0]
    · nlinarith [mul_le_mul_of_nonneg_left ha1 (by linarith : (0:ℝ) ≤ 1 - s),
        mul_le_mul_of_nonneg_left hb1 hs0]⟩

theorem affine_val (a b : unitInterval) (s : unitInterval) :
    (affine a b s : ℝ) = (1 - (s : ℝ)) * (a : ℝ) + (s : ℝ) * (b : ℝ) := by
  simp [affine]; ring

theorem affine_val' (a b : unitInterval) (s : unitInterval) :
    (affine a b s : ℝ) = (a : ℝ) + ((b : ℝ) - (a : ℝ)) * (s : ℝ) := rfl

theorem affine_zero (a b : unitInterval) : affine a b 0 = a := by
  ext; simp [affine]

theorem affine_one (a b : unitInterval) : affine a b 1 = b := by
  ext; simp [affine]

theorem continuous_affine (a b : unitInterval) : Continuous (affine a b) := by
  apply Continuous.subtype_mk
  · fun_prop

theorem affine_self (a : unitInterval) (s : unitInterval) : affine a a s = a := by
  ext; simp [affine]

/-- The restriction of a path to a subinterval `[a,b]` of the unit interval, reparametrized
affinely onto the whole unit interval.  It is a path from `γ a` to `γ b`. -/
def restr {x y : X} (γ : Path x y) (a b : unitInterval) : Path (γ a) (γ b) where
  toFun s := γ (affine a b s)
  continuous_toFun := γ.continuous.comp (continuous_affine a b)
  source' := by rw [affine_zero]
  target' := by rw [affine_one]

@[simp]
theorem restr_apply {x y : X} (γ : Path x y) (a b : unitInterval)
    (s : unitInterval) : γ.restr a b s = γ (affine a b s) := rfl

@[simp]
theorem restr_same {x y : X} (γ : Path x y) (a : unitInterval) :
    γ.restr a a = Path.refl (γ a) := by
  ext s
  rw [restr_apply]
  have h : affine a a s = a := by ext; simp [affine]
  rw [h]
  rfl

/-- Membership in a set is preserved by restriction. -/
theorem restr_mem {x y : X} (γ : Path x y) {a b : unitInterval} (hab : a ≤ b) {S : Set X}
    (hS : ∀ s ∈ Icc a b, γ s ∈ S) : ∀ s, γ.restr a b s ∈ S := by
  intro s
  rw [restr_apply]
  have hab' : (a:ℝ) ≤ b := hab
  have hs1 : (s:ℝ) ≤ 1 := s.2.2
  have ha0 : (0:ℝ) ≤ a := a.2.1
  have hb0 : (0:ℝ) ≤ b := b.2.1
  have hs0 : (0:ℝ) ≤ s := s.2.1
  refine hS (affine a b s) ⟨Subtype.coe_le_coe.mp ?_, Subtype.coe_le_coe.mp ?_⟩
  · rw [affine_val]; nlinarith
  · rw [affine_val]; nlinarith

/-! #### Splitting a path at an intermediate time -/

/-- The argument map of the concatenation `(γ.restr a b).trans (γ.restr b c)`, as a single
formula: it agrees with `affine a b` on the first half and with `affine b c` on the second. -/
def thetaVal (a b c : unitInterval) (s : unitInterval) : ℝ :=
  (a : ℝ) + ((b : ℝ) - (a : ℝ)) * min (2 * (s : ℝ)) 1 + ((c : ℝ) - (b : ℝ)) * max (2 * (s : ℝ) - 1) 0

theorem thetaVal_mem (a b c : unitInterval) (s : unitInterval) :
    thetaVal a b c s ∈ Icc (0:ℝ) 1 := by
  have ha0 : (0:ℝ) ≤ a := a.2.1
  have ha1 : (a:ℝ) ≤ 1 := a.2.2
  have hb0 : (0:ℝ) ≤ b := b.2.1
  have hb1 : (b:ℝ) ≤ 1 := b.2.2
  have hc0 : (0:ℝ) ≤ c := c.2.1
  have hc1 : (c:ℝ) ≤ 1 := c.2.2
  have hs0 : (0:ℝ) ≤ s := s.2.1
  have hs1 : (s:ℝ) ≤ 1 := s.2.2
  by_cases h : 2 * (s:ℝ) ≤ 1
  · rw [thetaVal, min_eq_left h, max_eq_right (by linarith), mul_zero, add_zero]
    have key : (a:ℝ) + ((b:ℝ) - (a:ℝ)) * (2 * (s:ℝ))
        = (1 - 2 * (s:ℝ)) * (a:ℝ) + (2 * (s:ℝ)) * (b:ℝ) := by ring
    rw [key]
    constructor
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - 2*s) ha0,
        mul_nonneg (by linarith : (0:ℝ) ≤ 2*s) hb0]
    · nlinarith [mul_le_mul_of_nonneg_left ha1 (by linarith : (0:ℝ) ≤ 1 - 2*s),
        mul_le_mul_of_nonneg_left hb1 (by linarith : (0:ℝ) ≤ 2*s)]
  · rw [thetaVal, min_eq_right (by linarith), max_eq_left (by linarith)]
    have key : (a:ℝ) + ((b:ℝ) - (a:ℝ)) * 1 + ((c:ℝ) - (b:ℝ)) * (2 * (s:ℝ) - 1)
        = (2 - 2 * (s:ℝ)) * (b:ℝ) + (2 * (s:ℝ) - 1) * (c:ℝ) := by ring
    rw [key]
    constructor
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 - 2*s) hb0,
        mul_nonneg (by linarith : (0:ℝ) ≤ 2*s - 1) hc0]
    · nlinarith [mul_le_mul_of_nonneg_left hb1 (by linarith : (0:ℝ) ≤ 2 - 2*s),
        mul_le_mul_of_nonneg_left hc1 (by linarith : (0:ℝ) ≤ 2*s - 1)]

def theta (a b c : unitInterval) (s : unitInterval) : unitInterval :=
  ⟨thetaVal a b c s, thetaVal_mem a b c s⟩

theorem continuous_thetaVal (a b c : unitInterval) : Continuous (thetaVal a b c) := by
  unfold thetaVal
  fun_prop

theorem continuous_theta (a b c : unitInterval) : Continuous (theta a b c) :=
  Continuous.subtype_mk (continuous_thetaVal a b c) (fun s => thetaVal_mem a b c s)

theorem theta_coe (a b c : unitInterval) (s : unitInterval) :
    (theta a b c s : ℝ) = thetaVal a b c s := rfl

theorem theta_zero (a b c : unitInterval) : theta a b c 0 = a := by
  ext
  rw [theta_coe, thetaVal]
  have h1 : ((0 : unitInterval) : ℝ) = 0 := rfl
  rw [h1]
  norm_num

theorem theta_one (a b c : unitInterval) : theta a b c 1 = c := by
  ext
  rw [theta_coe, thetaVal]
  have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
  rw [h1]
  norm_num

/-- **Splitting a path at an intermediate time.**  The path `γ` restricted to `[a,c]` is homotopic
to the concatenation of its restrictions to `[a,b]` and `[b,c]`. -/
theorem homotopic_restr_trans {x y : X} (γ : Path x y) (a b c : unitInterval) :
    Path.Homotopic (γ.restr a c) ((γ.restr a b).trans (γ.restr b c)) := by
  have htheta : Continuous fun p : unitInterval × unitInterval => theta a b c p.2 :=
    (continuous_theta a b c).comp continuous_snd
  have haff : Continuous fun p : unitInterval × unitInterval => affine a c p.2 :=
    (continuous_affine a c).comp continuous_snd
  have hcont1 : Continuous fun p : unitInterval × unitInterval =>
      ((theta a b c p.2 : unitInterval) : ℝ) :=
    continuous_subtype_val.comp htheta
  have hcont2 : Continuous fun p : unitInterval × unitInterval =>
      ((affine a c p.2 : unitInterval) : ℝ) :=
    continuous_subtype_val.comp haff
  have hcont3 : Continuous fun p : unitInterval × unitInterval => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  refine ⟨{
    toFun := fun p => γ (affine (affine a c p.2) (theta a b c p.2) p.1)
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · exact γ.continuous.comp (Continuous.subtype_mk
      (hcont2.add ((hcont1.sub hcont2).mul hcont3)) (fun p => (affine _ _ _).2))
  · intro s
    show γ (affine (affine a c s) (theta a b c s) 0) = γ.restr a c s
    rw [affine_zero, restr_apply]
  · intro s
    show γ (affine (affine a c s) (theta a b c s) 1) = ((γ.restr a b).trans (γ.restr b c)) s
    rw [affine_one, Path.trans_apply]
    by_cases hs : (s:ℝ) ≤ 1 / 2
    · rw [dif_pos hs, restr_apply]
      apply congrArg γ; ext
      have h1 : 2 * (s:ℝ) ≤ 1 := by linarith
      have h2 : 2 * (s:ℝ) - 1 ≤ 0 := by linarith
      rw [theta_coe, thetaVal, min_eq_left h1, max_eq_right h2, mul_zero, add_zero, affine_val]
      simp only [Subtype.coe_mk]
      ring
    · rw [dif_neg hs, restr_apply]
      apply congrArg γ; ext
      have h1 : 1 ≤ 2 * (s:ℝ) := by linarith
      have h2 : 0 ≤ 2 * (s:ℝ) - 1 := by linarith
      rw [theta_coe, thetaVal, min_eq_right h1, max_eq_left h2, affine_val]
      simp only [Subtype.coe_mk]
      ring
  · intro t s hs
    rcases hs with hs | hs
    · rw [hs]
      show γ (affine (affine a c 0) (theta a b c 0) t) = γ.restr a c 0
      rw [theta_zero, affine_zero, restr_apply, affine_zero]
      rw [affine_self]
    · rw [Set.mem_singleton_iff] at hs
      rw [hs]
      show γ (affine (affine a c 1) (theta a b c 1) t) = γ.restr a c 1
      rw [theta_one, affine_one, restr_apply, affine_one, affine_self]

end Path

namespace Path

variable {X : Type*} [TopologicalSpace X]

/-- A path inside a path-connected set joining two of its points. -/
theorem exists_path_of_isPathConnected {S : Set X} (hS : IsPathConnected S) {a b : X}
    (ha : a ∈ S) (hb : b ∈ S) : ∃ p : Path a b, ∀ s, p s ∈ S := by
  obtain ⟨c, hc, h⟩ := hS
  refine ⟨((h ha).symm.trans (h hb)).somePath, fun s => JoinedIn.somePath_mem _ s⟩

end Path

namespace Path

variable {X : Type*} [TopologicalSpace X]

/-- A loop in a simply connected set is null-homotopic in the ambient space. -/
theorem homotopic_refl_of_isSimplyConnected {S : Set X} (hS : IsSimplyConnected S)
    {a : X} (p : Path a a) (hp : ∀ s, p s ∈ S) :
    Path.Homotopic p (Path.refl a) := by
  obtain ⟨F, -⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hS).2 a p hp
  exact ⟨F⟩

/-- Two paths in a simply connected set with the same endpoints are homotopic in the ambient
space. -/
theorem homotopic_of_isSimplyConnected {S : Set X} (hS : IsSimplyConnected S)
    {a b : X} (ha : a ∈ S) (hb : b ∈ S) {p q : Path a b}
    (hp : ∀ s, p s ∈ S) (hq : ∀ s, q s ∈ S) : Path.Homotopic p q := by
  have hloop : Path.Homotopic (p.trans q.symm) (Path.refl a) :=
    homotopic_refl_of_isSimplyConnected hS _ (fun s => by
      rw [Path.trans_apply]
      split_ifs with h
      · exact hp _
      · exact hq _)
  have h1 : Path.Homotopic ((p.trans q.symm).trans q) ((Path.refl a).trans q) :=
    Path.Homotopic.hcomp hloop (Path.Homotopic.refl q)
  have h2 : Path.Homotopic ((p.trans q.symm).trans q) p :=
    (Path.Homotopic.trans_assoc p q.symm q).trans
      ((Path.Homotopic.hcomp (Path.Homotopic.refl p) (Path.Homotopic.symm_trans q)).trans
        (Path.Homotopic.trans_refl p))
  have h3 : Path.Homotopic ((Path.refl a).trans q) q := Path.Homotopic.refl_trans q
  exact h2.symm.trans (h1.trans h3)

end Path

namespace Work.Smooth.JordanSeparation

open OnePoint
open scoped OnePoint

/-- **Elementary van Kampen lemma.**  Let `U` and `V` be open subsets of a space `X` with simply
connected `U`, `V` and path connected `U ∩ V`, and let `x ∈ U ∩ V`.  Then every loop at `x` whose
image is contained in `U ∪ V` is null-homotopic. -/
theorem loop_nullhomotopic_of_cover {X : Type*} [TopologicalSpace X] {U V : Set X} {x : X}
    (hUo : IsOpen U) (hVo : IsOpen V) (hxU : x ∈ U) (hxV : x ∈ V)
    (hU : IsSimplyConnected U) (hV : IsSimplyConnected V)
    (hUV : IsPathConnected (U ∩ V))
    (γ : Path x x) (hγ : ∀ t, γ t ∈ U ∪ V) :
    Path.Homotopic γ (Path.refl x) := by
  classical
  -- the pullback cover of the unit interval
  set c : Bool → Set unitInterval := fun b => if b then γ ⁻¹' V else γ ⁻¹' U with hc
  have hc_open : ∀ b, IsOpen (c b) := by
    intro b; cases b
    · exact hUo.preimage γ.continuous
    · exact hVo.preimage γ.continuous
  have hc_cover : (univ : Set unitInterval) ⊆ ⋃ b, c b := by
    intro s _
    rcases hγ s with h | h
    · exact Set.mem_iUnion.mpr ⟨false, by simp [hc, h]⟩
    · exact Set.mem_iUnion.mpr ⟨true, by simp [hc, h]⟩
  obtain ⟨t, ht0, htmono, hfin, hlab⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc_open hc_cover
  -- the labels and the corresponding sets
  let lab : ℕ → Bool := fun n => Classical.choose (hlab n)
  have hlab' : ∀ n, Icc (t n) (t (n + 1)) ⊆ c (lab n) := fun n => Classical.choose_spec (hlab n)
  set W : Bool → Set X := fun b => if b then V else U with hW
  have hWlab : ∀ b, γ ⁻¹' W b = c b := by
    intro b; cases b <;> simp [hc, hW]
  have hWsc : ∀ b, IsSimplyConnected (W b) := by
    intro b; cases b <;> simp only [hW, if_true, if_false, Bool.false_eq_true] <;> assumption
  have hWpc : ∀ b, IsPathConnected (W b) := fun b => (hWsc b).isPathConnected
  have hWx : ∀ b, x ∈ W b := by
    intro b; cases b <;> simp only [hW, if_true, if_false, Bool.false_eq_true] <;> assumption
  have hWint : ∀ b b', IsPathConnected (W b ∩ W b') := by
    intro b b'
    cases b <;> cases b' <;>
      simp only [hW, if_true, if_false, Bool.false_eq_true]
    · simpa only [Set.inter_self] using hU.isPathConnected
    · exact hUV
    · simpa only [Set.inter_comm] using hUV
    · simpa only [Set.inter_self] using hV.isPathConnected
  have hγW : ∀ n, ∀ s ∈ Icc (t n) (t (n + 1)), γ s ∈ W (lab n) := by
    intro n s hs
    have h1 : s ∈ c (lab n) := hlab' n hs
    rwa [← hWlab] at h1
  -- the first index at which the subdivision reaches 1
  obtain ⟨N₀, hN₀⟩ := hfin
  have hex : ∃ n, t n = 1 := ⟨N₀, hN₀ N₀ le_rfl⟩
  let N := Nat.find hex
  have hNt : t N = 1 := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro h
    have h1 : t 0 = (1 : unitInterval) := by rw [← hNt, h]
    rw [ht0] at h1
    exact zero_ne_one h1
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  -- the induction
  have key : ∀ i : ℕ, 1 ≤ i → ∃ ω : Path (γ (t 0)) (γ (t i)),
      (∀ s, ω s ∈ W (lab (i - 1))) ∧ Path.Homotopic (γ.restr (t 0) (t i)) ω := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base =>
      refine ⟨γ.restr (t 0) (t 1), ?_, Path.Homotopic.refl _⟩
      intro s
      exact Path.restr_mem γ (htmono (Nat.zero_le 1)) (fun s hs => hγW 0 s hs) s
    | succ i hi ih =>
      obtain ⟨ω, hωmem, hωhom⟩ := ih
      have h0i : t 0 ≤ t i := htmono (Nat.zero_le i)
      have hii1 : t i ≤ t (i + 1) := htmono (Nat.le_succ i)
      have hstep : Path.Homotopic (γ.restr (t 0) (t (i + 1)))
          (ω.trans (γ.restr (t i) (t (i + 1)))) :=
        (Path.homotopic_restr_trans γ (t 0) (t i) (t (i + 1))).trans
          (Path.Homotopic.hcomp hωhom (Path.Homotopic.refl _))
      have haZ : γ (t 0) ∈ W (lab (i - 1)) ∩ W (lab i) := by
        constructor
        · have h : γ (t 0) = x := by rw [ht0]; exact γ.source
          rw [h]; exact hWx (lab (i - 1))
        · have h : γ (t 0) = x := by rw [ht0]; exact γ.source
          rw [h]; exact hWx (lab i)
      have hsub : i - 1 + 1 = i := Nat.sub_add_cancel hi
      have hbZ : γ (t i) ∈ W (lab (i - 1)) ∩ W (lab i) := by
        constructor
        · have hle : t (i - 1) ≤ t i := htmono (Nat.sub_le i 1)
          have h := hγW (i - 1) (t i) (by rw [hsub]; exact ⟨hle, le_rfl⟩)
          simpa only [hsub] using h
        · exact hγW i (t i) ⟨le_rfl, hii1⟩
      obtain ⟨ω', hω'mem⟩ := Path.exists_path_of_isPathConnected (hWint (lab (i-1)) (lab i)) haZ hbZ
      have hωω' : Path.Homotopic ω ω' :=
        Path.homotopic_of_isSimplyConnected (hWsc (lab (i - 1))) haZ.1 hbZ.1 hωmem
          (fun s => (hω'mem s).1)
      have hqmem : ∀ s, (γ.restr (t i) (t (i + 1))) s ∈ W (lab i) :=
        Path.restr_mem γ hii1 (fun s hs => hγW i s hs)
      refine ⟨ω'.trans (γ.restr (t i) (t (i + 1))), ?_, ?_⟩
      · intro s
        rw [Path.trans_apply]
        split_ifs with h
        · exact (hω'mem _).2
        · exact hqmem _
      · exact hstep.trans (Path.Homotopic.hcomp hωω' (Path.Homotopic.refl _))
  -- conclusion
  obtain ⟨ω, hωmem, hωhom⟩ := key N hN1
  have hγt0 : γ (t 0) = x := by rw [ht0]; exact γ.source
  have hγtN : γ (t N) = x := by rw [hNt]; exact γ.target
  set ωc : Path x x := ω.cast hγt0.symm hγtN.symm with hωcdef
  have hωc_mem : ∀ s, ωc s ∈ W (lab (N - 1)) := by
    intro s
    have h : ωc s = ω s := by rw [hωcdef]; simp
    rw [h]; exact hωmem s
  have hωcnull : Path.Homotopic ωc (Path.refl x) :=
    Path.homotopic_refl_of_isSimplyConnected (hWsc (lab (N - 1))) ωc hωc_mem
  have hcast : (γ.restr (t 0) (t N)).cast hγt0.symm hγtN.symm = γ := by
    ext s
    rw [Path.cast_coe, Path.restr_apply]
    apply congrArg γ; ext
    rw [Path.affine_val, ht0, hNt]
    norm_num
  have h2 : Path.Homotopic ((γ.restr (t 0) (t N)).cast hγt0.symm hγtN.symm) ωc := by
    obtain ⟨F⟩ := hωhom
    exact ⟨F.pathCast hγt0.symm hγtN.symm⟩
  rw [hcast] at h2
  exact h2.trans hωcnull

/-! ### The Riemann sphere -/


/-- The chart `ℂ = {∞}ᶜ` of the Riemann sphere is simply connected. -/
theorem isSimplyConnected_compl_infty : IsSimplyConnected ({∞}ᶜ : Set (OnePoint ℂ)) := by
  haveI : ContractibleSpace ↥(univ : Set ℂ) := Convex.contractibleSpace convex_univ ⟨0, trivial⟩
  have h : IsSimplyConnected ((↑) '' (univ : Set ℂ) : Set (OnePoint ℂ)) := by
    rw [Topology.IsEmbedding.isSimplyConnected_image
      (OnePoint.isOpenEmbedding_coe (X := ℂ)).toIsEmbedding (s := univ)]
    exact SimplyConnectedSpace.ofContractible _
  rwa [Set.image_univ, ← OnePoint.compl_infty] at h

/-- Every chart `{p}ᶜ` of the Riemann sphere at a finite point `p` is simply connected. -/
theorem isSimplyConnected_compl_coe (p : ℂ) : IsSimplyConnected ({↑p}ᶜ : Set (OnePoint ℂ)) := by
  set Φ : OnePoint ℂ ≃ₜ OnePoint ℂ :=
    Work.Smooth.SphereJordan.invHomeomorph.trans
      (Homeomorph.onePointCongr (Homeomorph.addRight p)) with hΦ
  have hΦp : Φ ∞ = (↑p : OnePoint ℂ) := by
    rw [hΦ, Homeomorph.trans_apply, Homeomorph.onePointCongr_apply]
    simp
  have hpre : Φ ⁻¹' ({↑p}ᶜ : Set (OnePoint ℂ)) = {∞}ᶜ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · intro h hy
      exact h (by rw [hy, hΦp])
    · intro h hy
      exact h (Φ.injective (by rw [hy, hΦp]))
  have h1 : IsSimplyConnected (Φ ⁻¹' ({↑p}ᶜ : Set (OnePoint ℂ))) := by
    rw [hpre]; exact isSimplyConnected_compl_infty
  exact (Homeomorph.isSimplyConnected_preimage Φ).mp h1

/-- `X \ {∞, q}` is path connected for every finite `q`. -/
theorem isPathConnected_infty_inter_coe (q : ℂ) :
    IsPathConnected ({∞}ᶜ ∩ {↑q}ᶜ : Set (OnePoint ℂ)) := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank ℝ ℂ, Complex.finrank_real_complex]
    norm_num
  have hset : ({∞}ᶜ ∩ {↑q}ᶜ : Set (OnePoint ℂ)) = (↑) '' ({q}ᶜ : Set ℂ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp (by simpa using hx.1)
      exact ⟨z, by simpa [← hz] using hx.2, hz⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨OnePoint.coe_ne_infty z, by simpa using hz⟩
  rw [hset]
  exact (isPathConnected_compl_singleton_of_one_lt_rank (E := ℂ) hrank q).image
    OnePoint.continuous_coe

/-- Every loop based at a finite point of the Riemann sphere is null-homotopic. -/
theorem loop_nullhomotopic_finite (z : ℂ) (γ : Path (↑z : OnePoint ℂ) ↑z) :
    Path.Homotopic γ (Path.refl (↑z : OnePoint ℂ)) := by
  have hxV : (↑z : OnePoint ℂ) ∈ ({↑(z + 1)}ᶜ : Set (OnePoint ℂ)) := by
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have h2 : z = z + 1 := OnePoint.coe_eq_coe.mp h
    have h3 : z + 1 = z + 0 := by simpa using h2.symm
    exact one_ne_zero (add_left_cancel h3)
  have hunion : ({∞}ᶜ ∪ {↑(z + 1)}ᶜ : Set (OnePoint ℂ)) = univ := by
    rw [← Set.compl_inter]
    simp [OnePoint.infty_ne_coe]
  refine loop_nullhomotopic_of_cover (U := {∞}ᶜ) (V := {↑(z + 1)}ᶜ) (x := (↑z : OnePoint ℂ))
    OnePoint.isClosed_infty.isOpen_compl isOpen_compl_singleton (OnePoint.coe_ne_infty z) hxV
    isSimplyConnected_compl_infty (isSimplyConnected_compl_coe (z + 1))
    (isPathConnected_infty_inter_coe (z + 1)) γ ?_
  intro t
  rw [hunion]
  exact Set.mem_univ _

/-- Every loop based at `∞` of the Riemann sphere is null-homotopic. -/
theorem loop_nullhomotopic_infty (γ : Path (∞ : OnePoint ℂ) ∞) :
    Path.Homotopic γ (Path.refl ∞) := by
  set ι : OnePoint ℂ ≃ₜ OnePoint ℂ := Work.Smooth.SphereJordan.invHomeomorph with hι
  have hι0 : ι ∞ = (↑(0 : ℂ) : OnePoint ℂ) := by
    rw [hι]; exact Work.Smooth.SphereJordan.invHomeomorph_infty
  have hι0' : ι (↑(0 : ℂ) : OnePoint ℂ) = ∞ := by
    rw [hι]; exact Work.Smooth.SphereJordan.invHomeomorph_coe_zero
  have hιι : ∀ y : OnePoint ℂ, ι (ι y) = y := by
    intro y
    rw [hι]
    exact Work.Smooth.SphereJordan.invMap_involutive y
  set γ' : Path (↑(0 : ℂ) : OnePoint ℂ) (↑(0 : ℂ) : OnePoint ℂ) :=
    (γ.map ι.continuous).cast hι0.symm hι0.symm with hγ'def
  have hfin : Path.Homotopic γ' (Path.refl (↑(0 : ℂ) : OnePoint ℂ)) :=
    loop_nullhomotopic_finite 0 γ'
  have hmap : Path.Homotopic (γ'.map ι.continuous)
      ((Path.refl (↑(0 : ℂ) : OnePoint ℂ)).map ι.continuous) :=
    Path.Homotopic.map hfin (⟨ι, ι.continuous⟩ : C(OnePoint ℂ, OnePoint ℂ))
  have hγ'' : (γ'.map ι.continuous).cast hι0'.symm hι0'.symm = γ := by
    ext s
    rw [Path.cast_coe, Path.map_coe]
    simp only [Function.comp_apply]
    rw [hγ'def]
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply]
    exact hιι (γ s)
  have hrefl : ((Path.refl (↑(0 : ℂ) : OnePoint ℂ)).map ι.continuous).cast hι0'.symm hι0'.symm
      = Path.refl ∞ := by
    ext s
    rw [Path.cast_coe, Path.map_coe]
    exact hι0'
  have hmap' : Path.Homotopic ((γ'.map ι.continuous).cast hι0'.symm hι0'.symm)
      (((Path.refl (↑(0 : ℂ) : OnePoint ℂ)).map ι.continuous).cast hι0'.symm hι0'.symm) :=
    Path.Homotopic.pathCast hmap hι0'.symm hι0'.symm
  rw [hγ'', hrefl] at hmap'
  exact hmap'

/-- **The Riemann sphere `OnePoint ℂ` is simply connected.** -/
theorem simplyConnectedSpace_onePoint_complex : SimplyConnectedSpace (OnePoint ℂ) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨?_, fun x γ => ?_⟩
  · haveI : LocallyPathConnectedSpace (OnePoint ℂ) := onePoint_locallyPathConnected
    exact PathConnectedSpace.of_locallyPathConnectedSpace
  · by_cases hx : x = ∞
    · subst hx
      exact loop_nullhomotopic_infty γ
    · obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hx
      exact loop_nullhomotopic_finite z γ

end Work.Smooth.JordanSeparation
