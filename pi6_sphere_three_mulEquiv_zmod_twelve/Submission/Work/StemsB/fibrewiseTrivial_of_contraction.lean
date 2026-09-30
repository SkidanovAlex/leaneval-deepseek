import Mathlib
import Submission.Work.StemsB.SerreSphereDefs
import Submission.Work.StemsB.HurewiczFibration

/-!
# Fibrewise triviality of a Hurewicz fibration over a contracted subset

Given a Hurewicz fibration `p : E → B`, a subset `W ⊆ B` and a point `d₀ ∈ W` together with an
explicit contraction `c : W × I → W` of `W` onto `d₀` (`c (w,0) = w`, `c (w,1) = d₀`, `d₀` fixed),
the restriction of `p` to `W` is **fibrewise trivial**: it is fibrewise homotopy equivalent over `W`
to the projection `W × p⁻¹(d₀) → W`.  This is the classical statement "a fibration over a
contractible base is (fibre homotopy) trivial" (Dold–Strøm), in the explicit Hurewicz form in which
it is used by the Serre exact sequence over a sphere (`Work.StemsB.FibrewiseTrivial`,
`Submission/Work/StemsB/SerreSphereDefs.lean`).

## The proof (prism argument)

The **prism** `P = {(e, w, t) : p e = c (w,t)} ⊆ E × (W × I)` is the pullback of `p` along
`c : W × I → B`, so the projection `P → W × I` is again a Hurewicz fibration
(`Work.StemsB.IsHurewiczFibration.pullbackSnd`).  Lifting the two contractions of the `t`-coordinate
of `W × I` (to `0` and to `1`) through `P → W × I`, starting at the identity of `P`, produces maps

* `prismG0 : P → P` landing in `P₀ = {t = 0}` together with a homotopy `prismH0 : id ≃ prismG0`
  covering `(w,t) ↦ (w, 0)`, and
* `prismG1 : P → P` landing in `P₁ = {t = 1}` together with a homotopy `prismH1 : id ≃ prismG1`
  covering `(w,t) ↦ (w, 1)`.

Both homotopies keep the `W`-coordinate fixed, so they are homotopies over `W`.  The two ends
`P₀ ≅ p⁻¹W` and `P₁ ≅ W × p⁻¹(d₀)` are the two spaces to be compared; the comparison maps are the
restrictions `Ψ = prismG0|_{P₁}`, `Φ = prismG1|_{P₀}` and the homotopies are the diagonal
composites

`H (x,s) = prismH0 (τ s, prismH1 (σ s, x))`,   `K (y,s) = prismH1 (τ s, prismH0 (σ s, y))`

with the reparametrisation `σ s = max (2s-1) 0`, `τ s = min (2s) 1` of `I`, chosen so that
`(1 - τ s) * σ s = 0`: this identity is exactly what makes the `t`-coordinate of `H` stay at `0`
(resp. `K` at `1`) — i.e. `H` (resp. `K`) is a homotopy of maps `p⁻¹W → p⁻¹W` (resp.
`W × p⁻¹(d₀) → W × p⁻¹(d₀)`) over `W`.
-/

open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
variable {W : Set B}

/-! ## Interval arithmetic

The two straight-line interpolations used for the reparametrisations, and the L-shaped
reparametrisation of `I × I` used for the diagonal composites. -/

/-- The interpolation `(1 - a) * b` between `b` and `0` in `I`. -/
def submul (a b : unitInterval) : unitInterval :=
  ⟨(1 - (a : ℝ)) * (b : ℝ), by
    rw [Set.mem_Icc]
    exact ⟨by nlinarith [a.2.1, a.2.2, b.2.1, b.2.2],
      by nlinarith [a.2.1, a.2.2, b.2.1, b.2.2]⟩⟩

/-- The interpolation `a + (1 - a) * b` between `b` and `1` in `I`. -/
def addmul (a b : unitInterval) : unitInterval :=
  ⟨(a : ℝ) + (1 - (a : ℝ)) * (b : ℝ), by
    rw [Set.mem_Icc]
    exact ⟨by nlinarith [a.2.1, a.2.2, b.2.1, b.2.2],
      by nlinarith [a.2.1, a.2.2, b.2.1, b.2.2]⟩⟩

theorem continuous_submul : Continuous fun p : unitInterval × unitInterval => submul p.1 p.2 :=
  Continuous.subtype_mk
    (f := fun p : unitInterval × unitInterval => (1 - (p.1 : ℝ)) * (p.2 : ℝ))
    (by fun_prop) (fun p => (submul p.1 p.2).2)

theorem continuous_addmul : Continuous fun p : unitInterval × unitInterval => addmul p.1 p.2 :=
  Continuous.subtype_mk
    (f := fun p : unitInterval × unitInterval => (p.1 : ℝ) + (1 - (p.1 : ℝ)) * (p.2 : ℝ))
    (by fun_prop) (fun p => (addmul p.1 p.2).2)

/-- `submul` as a continuous map of two variables. -/
def submulC : C(unitInterval × unitInterval, unitInterval) :=
  ⟨fun p => submul p.1 p.2, continuous_submul⟩

/-- `addmul` as a continuous map of two variables. -/
def addmulC : C(unitInterval × unitInterval, unitInterval) :=
  ⟨fun p => addmul p.1 p.2, continuous_addmul⟩

@[simp] theorem submul_zero_left (b : unitInterval) : submul 0 b = b := by ext; simp [submul]
@[simp] theorem submul_one_left (b : unitInterval) : submul 1 b = 0 := by ext; simp [submul]
@[simp] theorem submul_zero_right (a : unitInterval) : submul a 0 = 0 := by ext; simp [submul]
@[simp] theorem addmul_zero_left (b : unitInterval) : addmul 0 b = b := by ext; simp [addmul]
@[simp] theorem addmul_one_left (b : unitInterval) : addmul 1 b = 1 := by ext; simp [addmul]
@[simp] theorem addmul_zero_right (a : unitInterval) : addmul a 0 = a := by ext; simp [addmul]
@[simp] theorem addmul_one_right (a : unitInterval) : addmul a 1 = 1 := by ext; simp [addmul]

/-- `s ↦ min (2s) 1`, the "middle-to-end" reparametrisation `τ` of `I`. -/
def interpMid (s : unitInterval) : unitInterval :=
  ⟨min (2 * (s : ℝ)) 1, by
    rw [Set.mem_Icc]
    exact ⟨le_min (by linarith [s.2.1]) zero_le_one, min_le_right _ _⟩⟩

/-- `s ↦ max (2s - 1) 0`, the "end-to-middle" reparametrisation `σ` of `I`. -/
def interpEnd (s : unitInterval) : unitInterval :=
  ⟨max (2 * (s : ℝ) - 1) 0, by
    rw [Set.mem_Icc]
    exact ⟨le_max_right _ _, max_le (by linarith [s.2.2]) zero_le_one⟩⟩

theorem continuous_interpMid : Continuous interpMid :=
  Continuous.subtype_mk (f := fun s : unitInterval => min (2 * (s : ℝ)) 1)
    (by fun_prop) (fun s => (interpMid s).2)

theorem continuous_interpEnd : Continuous interpEnd :=
  Continuous.subtype_mk (f := fun s : unitInterval => max (2 * (s : ℝ) - 1) 0)
    (by fun_prop) (fun s => (interpEnd s).2)

/-- `interpMid` as a continuous map. -/
def interpMidC : C(unitInterval, unitInterval) := ⟨interpMid, continuous_interpMid⟩

/-- `interpEnd` as a continuous map. -/
def interpEndC : C(unitInterval, unitInterval) := ⟨interpEnd, continuous_interpEnd⟩

@[simp] theorem interpMid_zero : interpMid 0 = 0 := by ext <;> simp [interpMid] <;> norm_num
@[simp] theorem interpMid_one : interpMid 1 = 1 := by ext <;> simp [interpMid] <;> norm_num
@[simp] theorem interpEnd_zero : interpEnd 0 = 0 := by ext <;> simp [interpEnd] <;> norm_num
@[simp] theorem interpEnd_one : interpEnd 1 = 1 := by ext <;> simp [interpEnd] <;> norm_num

/-- **The L-shape.**  The two reparametrisations `τ = interpMid` and `σ = interpEnd` are
complementary in the sense that `(1 - τ s) * σ s = 0`: after the middle of `I` the outer
reparametrisation is `1`, before it the inner one is `0`. -/
theorem submul_interpMid_interpEnd (s : unitInterval) :
    submul (interpMid s) (interpEnd s) = 0 := by
  apply Subtype.ext
  show (1 - min (2 * (s : ℝ)) 1) * max (2 * (s : ℝ) - 1) 0 = 0
  rcases le_or_gt (2 * (s : ℝ)) 1 with h | h
  · have h' : 2 * (s : ℝ) - 1 ≤ 0 := by linarith
    rw [min_eq_left h, max_eq_right h']
    ring
  · rw [min_eq_right (le_of_lt h)]
    ring

/-- The companion identity: `τ s + (1 - τ s) * (1 - σ s) = 1`. -/
theorem addmul_interpMid_submul_interpEnd (s : unitInterval) :
    addmul (interpMid s) (submul (interpEnd s) 1) = 1 := by
  apply Subtype.ext
  have h : (1 - min (2 * (s:ℝ)) 1) * max (2 * (s:ℝ) - 1) 0 = 0 := by
    rcases le_or_gt (2 * (s:ℝ)) 1 with h | h
    · have h' : 2 * (s:ℝ) - 1 ≤ 0 := by linarith
      rw [min_eq_left h, max_eq_right h']
      ring
    · rw [min_eq_right (le_of_lt h)]
      ring
  show min (2 * (s:ℝ)) 1 + (1 - min (2 * (s:ℝ)) 1) * ((1 - max (2 * (s:ℝ) - 1) 0) * 1) = 1
  nlinarith [h]

/-! ## The prism -/

/-- The inclusion `↥W → B` as a continuous map. -/
def inclWB : C(↥W, B) := ⟨Subtype.val, continuous_subtype_val⟩

/-- `c`, read in the base `B`. -/
def prismBase (c : C(↥W × unitInterval, ↥W)) : C(↥W × unitInterval, B) :=
  inclWB.comp c

/-- **The prism** `{(e, w, t) : p e = c (w,t)}`: the pullback of `p` along the contraction. -/
abbrev Prism (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) : Type _ := Pullback p (prismBase c)

/-- The projection `Prism p c → ↥W × I`; it is a Hurewicz fibration. -/
def prismProj (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) : C(Prism p c, ↥W × unitInterval) :=
  pullbackSnd p (prismBase c)

/-- The `E`-coordinate of a prism point. -/
def prismE (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) : C(Prism p c, E) :=
  pullbackFst p (prismBase c)

/-- The `↥W`-coordinate of a prism point. -/
def prismW (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) : C(Prism p c, ↥W) :=
  ContinuousMap.fst.comp (prismProj p c)

/-- The `I`-coordinate of a prism point. -/
def prismT (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) : C(Prism p c, unitInterval) :=
  ContinuousMap.snd.comp (prismProj p c)

@[simp] theorem prismProj_apply (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (z : Prism p c) :
    prismProj p c z = z.1.2 := rfl

@[simp] theorem prismE_apply (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (z : Prism p c) :
    prismE p c z = z.1.1 := rfl

@[simp] theorem prismW_apply (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (z : Prism p c) :
    prismW p c z = z.1.2.1 := rfl

@[simp] theorem prismT_apply (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (z : Prism p c) :
    prismT p c z = z.1.2.2 := rfl

/-- The defining property of the prism. -/
theorem prism_mem (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (z : Prism p c) :
    p z.1.1 = (c z.1.2 : B) := z.2

/-! ## The two contractions of the prism -/

/-- The homotopy `(t, z) ↦ (w z, (1 - t) * t(z))` of the base `↥W × I` of the prism, contracting
the `I`-coordinate to `0`. -/
def prismK0 (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) :
    C(unitInterval × Prism p c, ↥W × unitInterval) :=
  ((prismW p c).comp ContinuousMap.snd).prodMk
    (submulC.comp (ContinuousMap.fst.prodMk ((prismT p c).comp ContinuousMap.snd)))

/-- The homotopy `(t, z) ↦ (w z, t + (1 - t) * t(z))` of the base `↥W × I` of the prism,
contracting the `I`-coordinate to `1`. -/
def prismK1 (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) :
    C(unitInterval × Prism p c, ↥W × unitInterval) :=
  ((prismW p c).comp ContinuousMap.snd).prodMk
    (addmulC.comp (ContinuousMap.fst.prodMk ((prismT p c).comp ContinuousMap.snd)))

@[simp] theorem prismK0_apply (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (t : unitInterval) (z : Prism p c) :
    prismK0 p c (t, z) = (z.1.2.1, submul t z.1.2.2) := rfl

@[simp] theorem prismK1_apply (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (t : unitInterval) (z : Prism p c) :
    prismK1 p c (t, z) = (z.1.2.1, addmul t z.1.2.2) := rfl

/-- The endpoint map of the first contraction: `z ↦ (w z, 0)`. -/
def prismZ0 (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) : C(Prism p c, ↥W × unitInterval) :=
  (prismW p c).prodMk (ContinuousMap.const (Prism p c) 0)

/-- The endpoint map of the second contraction: `z ↦ (w z, 1)`. -/
def prismZ1 (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) : C(Prism p c, ↥W × unitInterval) :=
  (prismW p c).prodMk (ContinuousMap.const (Prism p c) 1)

@[simp] theorem prismZ0_apply (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (z : Prism p c) :
    prismZ0 p c z = (z.1.2.1, 0) := rfl

@[simp] theorem prismZ1_apply (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (z : Prism p c) :
    prismZ1 p c z = (z.1.2.1, 1) := rfl

/-- The first contraction, as a homotopy of the base of the prism. -/
def prismHom0 (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) :
    ((prismProj p c).comp (ContinuousMap.id (Prism p c))).Homotopy (prismZ0 p c) :=
  ContinuousMap.Homotopy.mk (prismK0 p c)
    (fun z => by simp)
    (fun z => by simp)

/-- The second contraction, as a homotopy of the base of the prism. -/
def prismHom1 (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) :
    ((prismProj p c).comp (ContinuousMap.id (Prism p c))).Homotopy (prismZ1 p c) :=
  ContinuousMap.Homotopy.mk (prismK1 p c)
    (fun z => by simp)
    (fun z => by simp)

/-- The homotopy lifting property of the prism, for the contraction to `t = 0`. -/
theorem prism_lift0_exists (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hp : IsHurewiczFibration p) :
    ∃ (g : C(Prism p c, Prism p c)) (H : (ContinuousMap.id (Prism p c)).Homotopy g),
      (prismProj p c).comp H.toContinuousMap = prismK0 p c :=
  (IsHurewiczFibration.pullbackSnd (prismBase c) hp) (Prism p c)
    (ContinuousMap.id (Prism p c)) (prismZ0 p c) (prismHom0 p c)

/-- The homotopy lifting property of the prism, for the contraction to `t = 1`. -/
theorem prism_lift1_exists (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hp : IsHurewiczFibration p) :
    ∃ (g : C(Prism p c, Prism p c)) (H : (ContinuousMap.id (Prism p c)).Homotopy g),
      (prismProj p c).comp H.toContinuousMap = prismK1 p c :=
  (IsHurewiczFibration.pullbackSnd (prismBase c) hp) (Prism p c)
    (ContinuousMap.id (Prism p c)) (prismZ1 p c) (prismHom1 p c)

/-- The transport of the prism to `t = 0`. -/
def prismG0 (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (hp : IsHurewiczFibration p) :
    C(Prism p c, Prism p c) :=
  Classical.choose (prism_lift0_exists p c hp)

/-- The homotopy from the identity of the prism to `prismG0`, fibrewise over `↥W`. -/
def prismH0 (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (hp : IsHurewiczFibration p) :
    (ContinuousMap.id (Prism p c)).Homotopy (prismG0 p c hp) :=
  Classical.choose (Classical.choose_spec (prism_lift0_exists p c hp))

/-- The transport of the prism to `t = 1`. -/
def prismG1 (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (hp : IsHurewiczFibration p) :
    C(Prism p c, Prism p c) :=
  Classical.choose (prism_lift1_exists p c hp)

/-- The homotopy from the identity of the prism to `prismG1`, fibrewise over `↥W`. -/
def prismH1 (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (hp : IsHurewiczFibration p) :
    (ContinuousMap.id (Prism p c)).Homotopy (prismG1 p c hp) :=
  Classical.choose (Classical.choose_spec (prism_lift1_exists p c hp))

theorem prismH0_coverage (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hp : IsHurewiczFibration p) :
    (prismProj p c).comp (prismH0 p c hp).toContinuousMap = prismK0 p c :=
  Classical.choose_spec (Classical.choose_spec (prism_lift0_exists p c hp))

theorem prismH1_coverage (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hp : IsHurewiczFibration p) :
    (prismProj p c).comp (prismH1 p c hp).toContinuousMap = prismK1 p c :=
  Classical.choose_spec (Classical.choose_spec (prism_lift1_exists p c hp))

/-- The coordinates of the first lifted homotopy: it keeps the `↥W`-coordinate fixed and moves the
`I`-coordinate by `(1 - t) * ·`. -/
theorem prismH0_proj (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hp : IsHurewiczFibration p) (t : unitInterval) (z : Prism p c) :
    (prismH0 p c hp (t, z)).1.2 = (z.1.2.1, submul t z.1.2.2) := by
  have h := congrFun (congrArg DFunLike.coe (prismH0_coverage p c hp)) (t, z)
  simpa using h

/-- The coordinates of the second lifted homotopy. -/
theorem prismH1_proj (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hp : IsHurewiczFibration p) (t : unitInterval) (z : Prism p c) :
    (prismH1 p c hp (t, z)).1.2 = (z.1.2.1, addmul t z.1.2.2) := by
  have h := congrFun (congrArg DFunLike.coe (prismH1_coverage p c hp)) (t, z)
  simpa using h

@[simp] theorem prismH0_w (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hp : IsHurewiczFibration p) (t : unitInterval) (z : Prism p c) :
    (prismH0 p c hp (t, z)).1.2.1 = z.1.2.1 := by
  rw [prismH0_proj]

@[simp] theorem prismH0_t (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hp : IsHurewiczFibration p) (t : unitInterval) (z : Prism p c) :
    (prismH0 p c hp (t, z)).1.2.2 = submul t z.1.2.2 := by
  rw [prismH0_proj]

@[simp] theorem prismH1_w (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hp : IsHurewiczFibration p) (t : unitInterval) (z : Prism p c) :
    (prismH1 p c hp (t, z)).1.2.1 = z.1.2.1 := by
  rw [prismH1_proj]

@[simp] theorem prismH1_t (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hp : IsHurewiczFibration p) (t : unitInterval) (z : Prism p c) :
    (prismH1 p c hp (t, z)).1.2.2 = addmul t z.1.2.2 := by
  rw [prismH1_proj]

@[simp] theorem prismH0_zero (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hp : IsHurewiczFibration p) (z : Prism p c) : prismH0 p c hp (0, z) = z :=
  (prismH0 p c hp).map_zero_left z

@[simp] theorem prismH0_one (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hp : IsHurewiczFibration p) (z : Prism p c) : prismH0 p c hp (1, z) = prismG0 p c hp z :=
  (prismH0 p c hp).map_one_left z

@[simp] theorem prismH1_zero (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hp : IsHurewiczFibration p) (z : Prism p c) : prismH1 p c hp (0, z) = z :=
  (prismH1 p c hp).map_zero_left z

@[simp] theorem prismH1_one (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hp : IsHurewiczFibration p) (z : Prism p c) : prismH1 p c hp (1, z) = prismG1 p c hp z :=
  (prismH1 p c hp).map_one_left z

@[simp] theorem prismG0_w (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hp : IsHurewiczFibration p) (z : Prism p c) : (prismG0 p c hp z).1.2.1 = z.1.2.1 := by
  rw [← prismH0_one p c hp z, prismH0_w]

@[simp] theorem prismG0_t (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hp : IsHurewiczFibration p) (z : Prism p c) : (prismG0 p c hp z).1.2.2 = 0 := by
  rw [← prismH0_one p c hp z, prismH0_t, submul_one_left]

@[simp] theorem prismG1_w (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hp : IsHurewiczFibration p) (z : Prism p c) : (prismG1 p c hp z).1.2.1 = z.1.2.1 := by
  rw [← prismH1_one p c hp z, prismH1_w]

@[simp] theorem prismG1_t (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hp : IsHurewiczFibration p) (z : Prism p c) : (prismG1 p c hp z).1.2.2 = 1 := by
  rw [← prismH1_one p c hp z, prismH1_t, addmul_one_left]

/-- The `p`-value of a point of the first lifted homotopy. -/
theorem p_prismH0 (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (hp : IsHurewiczFibration p)
    (t : unitInterval) (z : Prism p c) :
    p (prismH0 p c hp (t, z)).1.1 = ((c (z.1.2.1, submul t z.1.2.2) : ↥W) : B) := by
  rw [prism_mem p c (prismH0 p c hp (t, z)), prismH0_proj p c hp t z]

/-- The `p`-value of a point of the second lifted homotopy. -/
theorem p_prismH1 (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (hp : IsHurewiczFibration p)
    (t : unitInterval) (z : Prism p c) :
    p (prismH1 p c hp (t, z)).1.1 = ((c (z.1.2.1, addmul t z.1.2.2) : ↥W) : B) := by
  rw [prism_mem p c (prismH1 p c hp (t, z)), prismH1_proj p c hp t z]

/-- The `p`-value of the endpoint of the first transport. -/
theorem p_prismG0 (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (hp : IsHurewiczFibration p)
    (z : Prism p c) : p (prismG0 p c hp z).1.1 = ((c (z.1.2.1, 0) : ↥W) : B) := by
  rw [← prismH0_one p c hp z, p_prismH0, submul_one_left]

/-- The `p`-value of the endpoint of the second transport. -/
theorem p_prismG1 (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (hp : IsHurewiczFibration p)
    (z : Prism p c) : p (prismG1 p c hp z).1.1 = ((c (z.1.2.1, 1) : ↥W) : B) := by
  rw [← prismH1_one p c hp z, p_prismH1, addmul_one_left]


/-! ## The two ends of the prism as maps into it -/

/-- The point of the prism over `x ∈ p ⁻¹' W` at time `0`. -/
def zPt0Fun (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (hc0 : ∀ w, c (w, 0) = w) :
    ↥(p ⁻¹' W) → Prism p c :=
  fun x => ⟨(x.1, (⟨p x.1, x.2⟩, (0 : unitInterval))), by
    show p x.1 = ((c (⟨p x.1, x.2⟩, (0 : unitInterval)) : ↥W) : B)
    rw [hc0]⟩

theorem continuous_zPt0Fun (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hc0 : ∀ w, c (w, 0) = w) : Continuous (zPt0Fun p c hc0) :=
  Continuous.subtype_mk
    (f := (fun x : ↥(p ⁻¹' W) => (x.1, (⟨p x.1, x.2⟩, (0 : unitInterval))) :
      ↥(p ⁻¹' W) → E × (↥W × unitInterval)))
    (by fun_prop)
    (fun x => by
      show p x.1 = ((c (⟨p x.1, x.2⟩, (0 : unitInterval)) : ↥W) : B)
      rw [hc0])

/-- The time-`0` end of the prism, as a continuous map. -/
def zPt0 (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (hc0 : ∀ w, c (w, 0) = w) :
    C(↥(p ⁻¹' W), Prism p c) := ⟨zPt0Fun p c hc0, continuous_zPt0Fun p c hc0⟩

/-- The point of the prism over `y ∈ W × p ⁻¹'(d₀)` at time `1`. -/
def zPt1Fun (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc1 : ∀ w, c (w, 1) = d₀) : ↥W × ↥(p ⁻¹' {d₀.1}) → Prism p c :=
  fun y => ⟨(y.2.1, (y.1, (1 : unitInterval))), by
    show p y.2.1 = ((c (y.1, (1 : unitInterval)) : ↥W) : B)
    exact y.2.2.trans (congrArg Subtype.val (hc1 y.1)).symm⟩

theorem continuous_zPt1Fun (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc1 : ∀ w, c (w, 1) = d₀) : Continuous (zPt1Fun p c d₀ hc1) :=
  Continuous.subtype_mk
    (f := (fun y : ↥W × ↥(p ⁻¹' {d₀.1}) => (y.2.1, (y.1, (1 : unitInterval))) :
      ↥W × ↥(p ⁻¹' {d₀.1}) → E × (↥W × unitInterval)))
    (by fun_prop)
    (fun y => by
      show p y.2.1 = ((c (y.1, (1 : unitInterval)) : ↥W) : B)
      exact y.2.2.trans (congrArg Subtype.val (hc1 y.1)).symm)

/-- The time-`1` end of the prism, as a continuous map. -/
def zPt1 (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc1 : ∀ w, c (w, 1) = d₀) :
    C(↥W × ↥(p ⁻¹' {d₀.1}), Prism p c) := ⟨zPt1Fun p c d₀ hc1, continuous_zPt1Fun p c d₀ hc1⟩

@[simp] theorem zPt0_e (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hc0 : ∀ w, c (w, 0) = w) (x : ↥(p ⁻¹' W)) : (zPt0 p c hc0 x).1.1 = x.1 := rfl

@[simp] theorem zPt0_w (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hc0 : ∀ w, c (w, 0) = w) (x : ↥(p ⁻¹' W)) :
    (zPt0 p c hc0 x).1.2.1 = ⟨p x.1, x.2⟩ := rfl

@[simp] theorem zPt0_t (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hc0 : ∀ w, c (w, 0) = w) (x : ↥(p ⁻¹' W)) : (zPt0 p c hc0 x).1.2.2 = 0 := rfl

@[simp] theorem zPt1_e (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc1 : ∀ w, c (w, 1) = d₀) (y : ↥W × ↥(p ⁻¹' {d₀.1})) :
    (zPt1 p c d₀ hc1 y).1.1 = y.2.1 := rfl

@[simp] theorem zPt1_w (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc1 : ∀ w, c (w, 1) = d₀) (y : ↥W × ↥(p ⁻¹' {d₀.1})) :
    (zPt1 p c d₀ hc1 y).1.2.1 = y.1 := rfl

@[simp] theorem zPt1_t (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc1 : ∀ w, c (w, 1) = d₀) (y : ↥W × ↥(p ⁻¹' {d₀.1})) :
    (zPt1 p c d₀ hc1 y).1.2.2 = 1 := rfl

/-! ## The two comparison maps -/

/-- The `p`-value of the forward transport of a point of `p ⁻¹' W` is `d₀`. -/
theorem p_prismG1_zPt0 (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (x : ↥(p ⁻¹' W)) : p (prismG1 p c hp (zPt0 p c hc0 x)).1.1 = d₀.1 := by
  rw [p_prismG1, zPt0_w]
  exact congrArg Subtype.val (hc1 ⟨p x.1, x.2⟩)

/-- The fibre component `Φ₀` of the trivialisation: the forward transport into the fibre over
`d₀`. -/
def phiEFun (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p) :
    ↥(p ⁻¹' W) → ↥(p ⁻¹' {d₀.1}) :=
  fun x => ⟨(prismG1 p c hp (zPt0 p c hc0 x)).1.1, p_prismG1_zPt0 p c d₀ hc0 hc1 hp x⟩

theorem continuous_phiEFun (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p) :
    Continuous (phiEFun p c d₀ hc0 hc1 hp) :=
  Continuous.subtype_mk
    (f := (fun x : ↥(p ⁻¹' W) => (prismG1 p c hp (zPt0 p c hc0 x)).1.1 :
      ↥(p ⁻¹' W) → E))
    ((prismE p c).continuous.comp ((prismG1 p c hp).continuous.comp (zPt0 p c hc0).continuous))
    (fun x => p_prismG1_zPt0 p c d₀ hc0 hc1 hp x)

def phiE (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p) :
    C(↥(p ⁻¹' W), ↥(p ⁻¹' {d₀.1})) :=
  ⟨phiEFun p c d₀ hc0 hc1 hp, continuous_phiEFun p c d₀ hc0 hc1 hp⟩

/-- The base component `x ↦ p x` of the trivialisation. -/
def phiW (p : C(E, B)) : C(↥(p ⁻¹' W), ↥W) :=
  ⟨fun x => ⟨p x.1, x.2⟩, Continuous.subtype_mk (p.continuous.comp continuous_subtype_val)
    (fun x => x.2)⟩

/-- The trivialisation `Φ : p ⁻¹' W → W × p ⁻¹'(d₀)`. -/
def phiMap (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p) :
    C(↥(p ⁻¹' W), ↥W × ↥(p ⁻¹' {d₀.1})) :=
  (phiW p).prodMk (phiE p c d₀ hc0 hc1 hp)

@[simp] theorem phiMap_fst (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (x : ↥(p ⁻¹' W)) : (phiMap p c d₀ hc0 hc1 hp x).1 = ⟨p x.1, x.2⟩ := rfl

@[simp] theorem phiMap_snd_val (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (x : ↥(p ⁻¹' W)) :
    ((phiMap p c d₀ hc0 hc1 hp x).2).1 = (prismG1 p c hp (zPt0 p c hc0 x)).1.1 := rfl

/-- The `p`-value of the backward transport of a point of `W × p ⁻¹'(d₀)` is the base point. -/
theorem p_prismG0_zPt1 (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (y : ↥W × ↥(p ⁻¹' {d₀.1})) : p (prismG0 p c hp (zPt1 p c d₀ hc1 y)).1.1 = (y.1 : B) := by
  rw [p_prismG0, zPt1_w]
  exact congrArg Subtype.val (hc0 y.1)

/-- The inverse trivialisation `Ψ : W × p ⁻¹'(d₀) → p ⁻¹' W` (on underlying points). -/
def psiFun (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p) :
    ↥W × ↥(p ⁻¹' {d₀.1}) → ↥(p ⁻¹' W) :=
  fun y => ⟨(prismG0 p c hp (zPt1 p c d₀ hc1 y)).1.1, by
    show p (prismG0 p c hp (zPt1 p c d₀ hc1 y)).1.1 ∈ W
    rw [p_prismG0_zPt1 p c d₀ hc0 hc1 hp y]
    exact y.1.2⟩

theorem continuous_psiFun (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p) :
    Continuous (psiFun p c d₀ hc0 hc1 hp) :=
  Continuous.subtype_mk
    (f := (fun y : ↥W × ↥(p ⁻¹' {d₀.1}) => (prismG0 p c hp (zPt1 p c d₀ hc1 y)).1.1 :
      ↥W × ↥(p ⁻¹' {d₀.1}) → E))
    ((prismE p c).continuous.comp ((prismG0 p c hp).continuous.comp (zPt1 p c d₀ hc1).continuous))
    (fun y => by
      show p (prismG0 p c hp (zPt1 p c d₀ hc1 y)).1.1 ∈ W
      rw [p_prismG0_zPt1 p c d₀ hc0 hc1 hp y]
      exact y.1.2)

/-- The inverse trivialisation `Ψ : W × p ⁻¹'(d₀) → p ⁻¹' W`. -/
def psiMap (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p) :
    C(↥W × ↥(p ⁻¹' {d₀.1}), ↥(p ⁻¹' W)) :=
  ⟨psiFun p c d₀ hc0 hc1 hp, continuous_psiFun p c d₀ hc0 hc1 hp⟩

@[simp] theorem psiMap_val (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (y : ↥W × ↥(p ⁻¹' {d₀.1})) :
    (psiMap p c d₀ hc0 hc1 hp y).1 = (prismG0 p c hp (zPt1 p c d₀ hc1 y)).1.1 := rfl

/-- The base condition for `Ψ`. -/
theorem p_psiMap (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (y : ↥W × ↥(p ⁻¹' {d₀.1})) : p (psiMap p c d₀ hc0 hc1 hp y).1 = (y.1 : B) :=
  p_prismG0_zPt1 p c d₀ hc0 hc1 hp y

/-- The two ends are related by the transports: `zPt1 ∘ Φ = G₁ ∘ zPt0`. -/
theorem zPt1_phiMap (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (x : ↥(p ⁻¹' W)) :
    zPt1 p c d₀ hc1 (phiMap p c d₀ hc0 hc1 hp x) = prismG1 p c hp (zPt0 p c hc0 x) := by
  refine Subtype.ext (Prod.ext rfl (Prod.ext ?_ ?_))
  · rw [zPt1_w, phiMap_fst, prismG1_w, zPt0_w]
  · rw [zPt1_t, prismG1_t]

/-- The two ends are related by the transports: `zPt0 ∘ Ψ = G₀ ∘ zPt1`. -/
theorem zPt0_psiMap (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (y : ↥W × ↥(p ⁻¹' {d₀.1})) :
    zPt0 p c hc0 (psiMap p c d₀ hc0 hc1 hp y) = prismG0 p c hp (zPt1 p c d₀ hc1 y) := by
  refine Subtype.ext (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · refine Subtype.ext ?_
    rw [zPt0_w, prismG0_w, zPt1_w]
    exact p_psiMap p c d₀ hc0 hc1 hp y
  · rw [zPt0_t, prismG0_t]

/-! ## The two homotopies -/

/-- The point of the prism at which the homotopy is evaluated. -/
def HInner (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (hc0 : ∀ w, c (w, 0) = w)
    (hp : IsHurewiczFibration p) :
    C(↥(p ⁻¹' W) × unitInterval, unitInterval × Prism p c) :=
  (interpMidC.comp (ContinuousMap.snd : C(↥(p ⁻¹' W) × unitInterval, unitInterval))).prodMk
    (((prismH1 p c hp).toContinuousMap).comp
      ((interpEndC.comp (ContinuousMap.snd : C(↥(p ⁻¹' W) × unitInterval, unitInterval))).prodMk
        ((zPt0 p c hc0).comp
          (ContinuousMap.fst : C(↥(p ⁻¹' W) × unitInterval, ↥(p ⁻¹' W))))))

@[simp] theorem HInner_apply (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hc0 : ∀ w, c (w, 0) = w) (hp : IsHurewiczFibration p)
    (q : ↥(p ⁻¹' W) × unitInterval) :
    HInner p c hc0 hp q = (interpMid q.2, prismH1 p c hp (interpEnd q.2, zPt0 p c hc0 q.1)) :=
  rfl

/-- The `E`-coordinate of the homotopy `H` on `p ⁻¹' W`. -/
def HOuter (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (hc0 : ∀ w, c (w, 0) = w)
    (hp : IsHurewiczFibration p) : C(↥(p ⁻¹' W) × unitInterval, E) :=
  (prismE p c).comp (((prismH0 p c hp).toContinuousMap).comp (HInner p c hc0 hp))

@[simp] theorem HOuter_apply (p : C(E, B)) (c : C(↥W × unitInterval, ↥W))
    (hc0 : ∀ w, c (w, 0) = w) (hp : IsHurewiczFibration p)
    (q : ↥(p ⁻¹' W) × unitInterval) :
    HOuter p c hc0 hp q = (prismH0 p c hp (HInner p c hc0 hp q)).1.1 := rfl

/-- The base computation for `H`: the homotopy stays over `p x`. -/
theorem p_HHom (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (q : ↥(p ⁻¹' W) × unitInterval) :
    p (prismH0 p c hp
        (interpMid q.2, prismH1 p c hp (interpEnd q.2, zPt0 p c hc0 q.1))).1.1 = p q.1.1 := by
  rw [p_prismH0, prismH1_w, prismH1_t, zPt0_w, zPt0_t, addmul_zero_right,
    submul_interpMid_interpEnd]
  exact congrArg Subtype.val (hc0 ⟨p q.1.1, q.1.2⟩)

/-- The homotopy `H : p ⁻¹' W × I → p ⁻¹' W` over `W` (on underlying points). -/
def HHFun (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p) :
    ↥(p ⁻¹' W) × unitInterval → ↥(p ⁻¹' W) :=
  fun q => ⟨HOuter p c hc0 hp q, by
    show p (HOuter p c hc0 hp q) ∈ W
    rw [HOuter_apply, HInner_apply]
    rw [p_HHom p c d₀ hc0 hc1 hp q]
    exact q.1.2⟩

theorem continuous_HHFun (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p) :
    Continuous (HHFun p c d₀ hc0 hc1 hp) :=
  Continuous.subtype_mk
    (f := (HOuter p c hc0 hp : ↥(p ⁻¹' W) × unitInterval → E))
    (HOuter p c hc0 hp).continuous
    (fun q => by
      show p (HOuter p c hc0 hp q) ∈ W
      rw [HOuter_apply, HInner_apply]
      rw [p_HHom p c d₀ hc0 hc1 hp q]
      exact q.1.2)

/-- The homotopy `H : p ⁻¹' W × I → p ⁻¹' W` from the identity to `Ψ ∘ Φ`. -/
def HHom (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p) :
    C(↥(p ⁻¹' W) × unitInterval, ↥(p ⁻¹' W)) :=
  ⟨HHFun p c d₀ hc0 hc1 hp, continuous_HHFun p c d₀ hc0 hc1 hp⟩

@[simp] theorem HHom_val (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (q : ↥(p ⁻¹' W) × unitInterval) :
    (HHom p c d₀ hc0 hc1 hp q).1 = HOuter p c hc0 hp q := rfl

theorem HHom_zero (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (x : ↥(p ⁻¹' W)) : HHom p c d₀ hc0 hc1 hp (x, 0) = x := by
  refine Subtype.ext ?_
  rw [HHom_val, HOuter_apply, HInner_apply]
  simp only [interpMid_zero, interpEnd_zero, prismH1_zero, prismH0_zero, zPt0_e]

theorem HHom_one (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (x : ↥(p ⁻¹' W)) :
    HHom p c d₀ hc0 hc1 hp (x, 1) = psiMap p c d₀ hc0 hc1 hp (phiMap p c d₀ hc0 hc1 hp x) := by
  refine Subtype.ext ?_
  rw [HHom_val, HOuter_apply, HInner_apply]
  simp only [interpMid_one, interpEnd_one, prismH1_one, prismH0_one, psiMap_val, zPt1_phiMap]

/-- The base condition for `H`. -/
theorem p_HHom' (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (x : ↥(p ⁻¹' W)) (t : unitInterval) : p (HHom p c d₀ hc0 hc1 hp (x, t)).1 = p x.1 := by
  rw [HHom_val, HOuter_apply, HInner_apply]
  exact p_HHom p c d₀ hc0 hc1 hp (x, t)

/-! ## The homotopy on `W × p ⁻¹'(d₀)` -/

/-- The point of the prism at which the second homotopy is evaluated. -/
def KInner (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p) :
    C((↥W × ↥(p ⁻¹' {d₀.1})) × unitInterval, unitInterval × Prism p c) :=
  (interpMidC.comp (ContinuousMap.snd :
      C((↥W × ↥(p ⁻¹' {d₀.1})) × unitInterval, unitInterval))).prodMk
    (((prismH0 p c hp).toContinuousMap).comp
      ((interpEndC.comp (ContinuousMap.snd :
          C((↥W × ↥(p ⁻¹' {d₀.1})) × unitInterval, unitInterval))).prodMk
        ((zPt1 p c d₀ hc1).comp (ContinuousMap.fst :
          C((↥W × ↥(p ⁻¹' {d₀.1})) × unitInterval, ↥W × ↥(p ⁻¹' {d₀.1}))))))

@[simp] theorem KInner_apply (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (q : (↥W × ↥(p ⁻¹' {d₀.1})) × unitInterval) :
    KInner p c d₀ hc1 hp q
      = (interpMid q.2, prismH0 p c hp (interpEnd q.2, zPt1 p c d₀ hc1 q.1)) := rfl

/-- The `E`-coordinate of the homotopy `K` on `W × p ⁻¹'(d₀)`. -/
def KOuter (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p) :
    C((↥W × ↥(p ⁻¹' {d₀.1})) × unitInterval, E) :=
  (prismE p c).comp (((prismH1 p c hp).toContinuousMap).comp (KInner p c d₀ hc1 hp))

@[simp] theorem KOuter_apply (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (q : (↥W × ↥(p ⁻¹' {d₀.1})) × unitInterval) :
    KOuter p c d₀ hc1 hp q = (prismH1 p c hp (KInner p c d₀ hc1 hp q)).1.1 := rfl

/-- The base computation for `K`: the homotopy stays over `d₀`. -/
theorem p_KHom (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (q : (↥W × ↥(p ⁻¹' {d₀.1})) × unitInterval) :
    p (prismH1 p c hp
        (interpMid q.2, prismH0 p c hp (interpEnd q.2, zPt1 p c d₀ hc1 q.1))).1.1 = d₀.1 := by
  rw [p_prismH1, prismH0_w, prismH0_t, zPt1_w, zPt1_t, addmul_interpMid_submul_interpEnd]
  exact congrArg Subtype.val (hc1 q.1.1)

/-- The homotopy `K : (W × p ⁻¹'(d₀)) × I → W × p ⁻¹'(d₀)` over `W`. -/
def KHFun (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p) :
    (↥W × ↥(p ⁻¹' {d₀.1})) × unitInterval → ↥W × ↥(p ⁻¹' {d₀.1}) :=
  fun q => (q.1.1, ⟨KOuter p c d₀ hc1 hp q, by
    show p (KOuter p c d₀ hc1 hp q) = d₀.1
    rw [KOuter_apply, KInner_apply]
    exact p_KHom p c d₀ hc0 hc1 hp q⟩)

theorem continuous_KHFun (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p) :
    Continuous (KHFun p c d₀ hc0 hc1 hp) :=
  Continuous.prodMk
    (by fun_prop : Continuous fun q : (↥W × ↥(p ⁻¹' {d₀.1})) × unitInterval => q.1.1)
    (Continuous.subtype_mk
      (f := (KOuter p c d₀ hc1 hp : (↥W × ↥(p ⁻¹' {d₀.1})) × unitInterval → E))
      (KOuter p c d₀ hc1 hp).continuous
      (fun q => by
        show p (KOuter p c d₀ hc1 hp q) = d₀.1
        rw [KOuter_apply, KInner_apply]
        exact p_KHom p c d₀ hc0 hc1 hp q))

/-- The homotopy `K : (W × p ⁻¹'(d₀)) × I → W × p ⁻¹'(d₀)` from the identity to `Φ ∘ Ψ`. -/
def KHom (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p) :
    C((↥W × ↥(p ⁻¹' {d₀.1})) × unitInterval, ↥W × ↥(p ⁻¹' {d₀.1})) :=
  ⟨KHFun p c d₀ hc0 hc1 hp, continuous_KHFun p c d₀ hc0 hc1 hp⟩

@[simp] theorem KHom_fst (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (q : (↥W × ↥(p ⁻¹' {d₀.1})) × unitInterval) :
    (KHom p c d₀ hc0 hc1 hp q).1 = q.1.1 := rfl

@[simp] theorem KHom_val (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (q : (↥W × ↥(p ⁻¹' {d₀.1})) × unitInterval) :
    (KHom p c d₀ hc0 hc1 hp q).2.1 = KOuter p c d₀ hc1 hp q := rfl

theorem KHom_zero (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (y : ↥W × ↥(p ⁻¹' {d₀.1})) : KHom p c d₀ hc0 hc1 hp (y, 0) = y := by
  refine Prod.ext ?_ ?_
  · rw [KHom_fst]
  · refine Subtype.ext ?_
    rw [KHom_val, KOuter_apply, KInner_apply]
    simp only [interpMid_zero, interpEnd_zero, prismH0_zero, prismH1_zero, zPt1_e]

theorem KHom_one (p : C(E, B)) (c : C(↥W × unitInterval, ↥W)) (d₀ : ↥W)
    (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = d₀) (hp : IsHurewiczFibration p)
    (y : ↥W × ↥(p ⁻¹' {d₀.1})) :
    KHom p c d₀ hc0 hc1 hp (y, 1) = phiMap p c d₀ hc0 hc1 hp (psiMap p c d₀ hc0 hc1 hp y) := by
  refine Prod.ext ?_ ?_
  · refine Subtype.ext ?_
    rw [KHom_fst, phiMap_fst]
    exact (p_psiMap p c d₀ hc0 hc1 hp y).symm
  · refine Subtype.ext ?_
    rw [KHom_val, KOuter_apply, KInner_apply]
    simp only [interpMid_one, interpEnd_one, prismH0_one, prismH1_one, phiMap_snd_val,
      zPt0_psiMap]

end
/-- **Fibrewise triviality over a contracted subset.**  A Hurewicz fibration `p : E → B` is
fibrewise trivial over a subset `W ⊆ B` that admits an explicit contraction onto a fixed point
`d₀ ∈ W`.  This is the explicit form of Dold's theorem ("a fibration over a contractible base is
fibre homotopy trivial") used by the Serre exact sequence over a sphere. -/
theorem fibrewiseTrivial_of_contraction {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : ContinuousMap E B) (hp : Work.StemsB.IsHurewiczFibration p) (W : Set B) (d₀ : ↥W)
    (c : ContinuousMap (↥W × unitInterval) ↥W) (hc0 : ∀ w, c (w, 0) = w)
    (hc1 : ∀ w, c (w, 1) = d₀) (hcb : ∀ t, c (d₀, t) = d₀) :
    Work.StemsB.FibrewiseTrivial p W d₀ := by
  refine ⟨phiMap p c d₀ hc0 hc1 hp, psiMap p c d₀ hc0 hc1 hp, ?_, ?_,
    ⟨HHom p c d₀ hc0 hc1 hp, ?_, ?_, ?_⟩,
    ⟨KHom p c d₀ hc0 hc1 hp, ?_, ?_, ?_⟩⟩
  · intro x; rfl
  · exact p_psiMap p c d₀ hc0 hc1 hp
  · exact HHom_zero p c d₀ hc0 hc1 hp
  · exact HHom_one p c d₀ hc0 hc1 hp
  · intro x t; exact p_HHom' p c d₀ hc0 hc1 hp x t
  · exact KHom_zero p c d₀ hc0 hc1 hp
  · exact KHom_one p c d₀ hc0 hc1 hp
  · intro y t; rfl

end Work.StemsB
