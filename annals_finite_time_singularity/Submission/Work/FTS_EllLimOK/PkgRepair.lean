/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.PkgRepair` — RETIRED fields (the lead's ruling of 2026-10-11)

**STATUS.**  Of the six fields of `HasPkgE` below, only `PkgCos` survived the ruling: the other five
are **false** and are kept here only as the record of the failed repair.

* `PkgMemSq` / `PkgSlice` — false by **homogeneity**: `HkSq` is quadratic in `g` while the bound
  `Ce·Xn6 α g` is linear (`RulingELF.pkgMemSq_degenerate`, `not_hasPkgF_of_pos`, machine-checked).
  Replaced by `RulingELF.PkgMemSqH` (bound `Ce·Xn6²`, `z`-local slice bound).
* `PkgDecay` — false: class `C` allows `z^{-s}` tails, `s ∈ (1/2,3/2)`, and `bslOp` is Euler in `z`,
  so `E g` inherits a `z^{-s}` tail and no `1/(1+z)` rate holds.  (`Defs3.LocalBound4`'s rate is
  false for the same reason.)
* `PkgStrip` — false: `g = χ(z)·z^s·φ(θ)`, `s ∈ (3/2,2)`, is in class `C` and `E g ~ z^s` is not
  `C²` at `z = 0`.
* `PkgCorner` — false: same `z^s` source makes `∂_z²E g ~ z^{s-2}` unbounded; and `g ~ θ^σ`,
  `σ ∈ (α/20, 1)`, is in class `C` with `∂_θ³E g ~ θ^{σ-1}`.

Replaced by the installed `RulingELF.HasPkgH := HasPkg ∧ PkgCos ∧ PkgMemSqH ∧ PkgBoxH`; the
consumers of the *false* fields (`LocalBound4D`, `SmallLocalBound4D`, `HasPkgD`, `HasPkgE` and the
`FatouG`/`ClosedCompact3G_of_bounds_fatou`/`SmallAssemblyG`/`MainG` chain) are superseded by
`FatouH`, `ClosedCompact3H_of_bounds_fatou`, `SmallAssemblyH`, `MainH`.

## The original header (kept for the record)

# `FTS_EllLimOK.PkgRepair` — the two fields that the packages provably lack

Obligation 1 of this area is `SmallLocalBound4 ∧ SmallFatouData` **from** `HasPkg α Ce E`.  The
mathematical half of it is proved (`PkgJets/pkg_pointwise_jets`: from `HasPkg` + `LimSeq4` + one
boundary datum, one constant bounds every order-`≤ 4` jet of `E (fn n)` uniformly in `n, z, θ`).
The two remaining data are provably **not** in `HasPkg`:

* **pinning — GAP A.**  `KernelObstruction/hasPkg_add_cex` shows that for every `E` with `HasPkg`
  and every linear `ℓ ≠ 0` on the class, the sibling `E' g = E g + ℓ g • cex α` again has `HasPkg`,
  where `cex α z θ = if θ = 0 then 0 else z^{-(3/α)}/cos θ` is an exact solution of the law
  (`StrongEps.EComparison.ScrRef5.cex_bslOp`) and of all three *linear* coefficient equations
  (`Uop_mode`/`Vop_mode`/`Rop_mode`).  So the packages see `E` only up to a one-dimensional kernel,
  and the reconstruction `Ψ = -(1/cos θ)∫_θ^{π/2} cos s·(Vop Ψ)(z,s) ds` — hence every pointwise
  bound on the jets of `E g` — needs one more datum: the *value* `lim_{θ→π/2} cos θ·Φ̃(z,θ) = 0`.
  **Field `PkgCos` below states exactly that datum.**  (The membership is stated for `PhiTil`, not
  for `E g`: `PhiTil α g (E g) = E g - Theta α g` and `Theta α g/cos θ = (1/2α) sin θ·L₁₂ g` is
  *not* `ℋ⁰` for a general class-`C` source, so the field has to be imposed on `PhiTil`.)
* **far-field rate — GAP B.**  The `ℋ`-weight is `w(z) = (1+z)²/z² → 1` at `z = ∞`, so no weighted
  `L²`-bound in `HasPkg` forces a *rate*, while `LocalBound4` (and `FatouData`'s decay clause) need
  one (`ClosedCompact3_of_bounds_fatou` uses it for the limit's `z → ∞` clause, Arzelà–Ascoli
  converging only on compacta).  **Field `PkgDecay` below states exactly that rate**, in the
  relative form `≤ K·Xn6 α g` that makes it uniform along a `LimSeq4`
  (`LimSeq4.bound : Xn6 α (fn n) ≤ B`).

`HasPkgD` is their conjunction with `HasPkg`.  It is the hypothesis under which this area derives
`Defs3.LocalBound4` and `Defs3.FatouData` (see `PkgJets/`), i.e. it is the *repair* of the frozen
`Work.FTS.VocabO.EllPkgGo` / `Work.FTS.ClassC.EllPkgK`; appending the two fields keeps every
existing projection of the packages intact (the `BoxReg` repair of the previous stretch used the
same device).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.Defs
import Submission.Work.FTS_EllLimOK.Defs3
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.FTS.StrongGlobal.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The pinning field**: the solution's `PhiTil`-part times `1/cos θ` is honestly in `ℋ⁰`.  This
is precisely the field of `FatouPkg` (item (12) of the tree's `EllipticEst.EllHyp`) that kills the
homogeneous mode `z^{-3/α}/cos θ`, which `HasPkg` alone cannot see
(`KernelObstruction.hasPkg_add_cex`).  It is endorsed by the lead's ruling of 2026-10-11 and is
field `PkgCos` of the installed honest hypothesis `RulingELF.HasPkgH`; it is *produced* by
`ProducerH.pkgCos_of_ellClassOk` (L1) from route (b).

(This field is the *only* one of the original `PkgRepair` fields that survived: the docstring that
used to claim that `Theta α g/cos θ` is not in `ℋ⁰` was **wrong** — `Theta α g/cos θ =
(1/(2α))·sin θ·L₁₂ g` is bounded by `|L₁₂ g|`, and `Theta` has a bound of its own
(`PkgJets.thetaBound`); `PkgMemSq`/`PkgSlice`/`PkgDecay`/`PkgStrip`/`PkgCorner` are all false and
are retired below. -/
def PkgCos (α : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  ∀ g, Work.FTS.ClassC.ClassC α g →
    Work.Spaces.HkMem α 0 (fun z θ => Work.Construction.PhiTil α g (E g) z θ / Real.cos θ)

/-- **The far-field rate field**: on the open quadrant the order-`≤ 4` jets of `E g` decay at least
like `(1+z)^{-3/2}`, *relative* to the `ℋ⁶`-norm of the source — the relative form is what makes the
bound uniform along a `LimSeq4` (`LimSeq4.bound : Xn6 α (fn n) ≤ B`).

The rate `3/2` (not `1`) is the one `FatouData`'s decay clause asks for (`j+i ≤ 2`), and it is
*also* all `LocalBound4` needs (`(1+z) ≤ (1+z)^{3/2}` for `z ≥ 0`), so a single field covers both.
`§ LocalBound4` below derives the `(1+z)^{-1}` form used by `LocalBound4`. -/
def PkgDecay (α : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ g, Work.FTS.ClassC.ClassC α g →
    ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      (1 + z) ^ (3 / 2 : ℝ) * |Work.Spaces.mixed j i (E g) z θ|
        ≤ K * Work.FTS.StrongGlobal.Xn6 α g

/-- **The closed-strip regularity field**: the solution is `C^∞` on a *neighbourhood* of the closed
quadrant, i.e. it has boundary traces of all orders.  This is what `FTS_EllLimOK.BoxReg_of_uniform`
consumes (as `Work.Spaces.SmoothStrip`) to produce `FatouData`'s `BoxData` clause: `SmoothOpen` is
an open-quadrant statement, and the upper bounds of `PkgDecay` give no equicontinuity at
`θ = 0, π/2` (the bound on `mixed 0 1 = sin(2θ)∂_θ` does not bound `∂_θ` where `sin(2θ) → 0`). -/
def PkgStrip (α : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  ∀ g, Work.FTS.ClassC.ClassC α g → Work.Spaces.SmoothStrip (E g)

/-- **The repaired package hypothesis**: the frozen two packages plus the three fields that they
provably lack. -/
def HasPkgD (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  HasPkg α Ce E ∧ PkgCos α E ∧ PkgDecay α E ∧ PkgStrip α E

theorem HasPkgD.toHasPkg {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgD α Ce E) :
    HasPkg α Ce E := h.1

theorem HasPkgD.cos {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgD α Ce E) :
    PkgCos α E := h.2.1

theorem HasPkgD.decay {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgD α Ce E) :
    PkgDecay α E := h.2.2.1

theorem HasPkgD.strip {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgD α Ce E) :
    PkgStrip α E := h.2.2.2

/-- `HasPkg` alone is the first component (the round trip used by the consumers). -/
theorem hasPkgD_of_parts {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkg α Ce E)
    (hc : PkgCos α E) (hd : PkgDecay α E) (hs : PkgStrip α E) : HasPkgD α Ce E :=
  ⟨h, hc, hd, hs⟩

/-! ## The `LocalBound4` reduction under the repaired hypothesis

Once the far-field rate is a field of the package, `Defs3.LocalBound4`'s body follows immediately:
the field gives `(1+z)|mixed j i (E g)| ≤ K·Xn6 α g`, `LimSeq4` gives `Xn6 α (fn n) ≤ B`, and the
extra factors `(1 + 1/z + 1/(θ(π/2-θ)))` are ≥ 1.  The *pointwise* half of `LocalBound4` (no decay)
is the content of `PkgJets/pkg_pointwise_jets`; the decay half is exactly the field, and it has to
be stated on the jets of `E g` (not on the slots): `Theta α g = (1/4α) sin 2θ·L₁₂ g` decays only as
fast as the *source* does, and class `C` only gives `g = o(z^{-1/2})`
(`ClassC.tr : BdryTraces α 6 g`, `ClassC.mem : HkMem α 7 g`), so no field on the slots can make the
`Theta`-part decay like `1/(1+z)`. -/
theorem localBound4_of_hasPkgD {α Ce : ℝ} (_hα : 0 < α) :
    ∀ E : Fn →ₗ[ℝ] Fn, HasPkgD α Ce E → ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ,
        (z, θ) ∈ Work.Construction.Qd →
        |Work.Spaces.mixed j i (E (fn n)) z θ|
          ≤ C * (1 + 1 / z + 1 / (θ * (π / 2 - θ))) / (1 + z) := by
  intro E hE fn f hL
  obtain ⟨K, hKpos, hKD⟩ := hE.decay
  obtain ⟨B, hB⟩ := hL.bound
  refine ⟨K * max B 0 + 1, by positivity, ?_⟩
  intro n j i hji z θ hzθ
  have hz : 0 < z := hzθ.1
  have hθ : 0 < θ := hzθ.2.1
  have hθ2 : θ < π / 2 := hzθ.2.2
  have hδ : 0 < π / 2 - θ := by linarith
  have hBle : Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ max B 0 :=
    le_trans (hB n) (le_max_left _ _)
  have hXnn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α (fn n) := Work.Spaces.HkNorm_nonneg α 6 (fn n)
  have hmaxnn : 0 ≤ max B 0 := le_max_right _ _
  have h1 := hKD (fn n) (hL.classC n) j i hji z θ hzθ
  have hz1 : 0 < 1 + z := by linarith
  have hsp : (1 : ℝ) ≤ (1 + z) ^ ((1 : ℝ) / 2) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hrw : (1 + z) ^ (3 / 2 : ℝ) = (1 + z) * (1 + z) ^ ((1 : ℝ) / 2) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
  have h2 : (1 + z) * |Work.Spaces.mixed j i (E (fn n)) z θ| ≤ K * max B 0 := by
    have hmono : (1 + z) * |Work.Spaces.mixed j i (E (fn n)) z θ|
        ≤ (1 + z) ^ (3 / 2 : ℝ) * |Work.Spaces.mixed j i (E (fn n)) z θ| := by
      rw [hrw]
      have hnn : (0 : ℝ) ≤ |Work.Spaces.mixed j i (E (fn n)) z θ| := abs_nonneg _
      calc (1 + z) * |Work.Spaces.mixed j i (E (fn n)) z θ|
          = 1 * ((1 + z) * |Work.Spaces.mixed j i (E (fn n)) z θ|) := by ring
        _ ≤ (1 + z) ^ ((1 : ℝ) / 2)
              * ((1 + z) * |Work.Spaces.mixed j i (E (fn n)) z θ|) :=
            mul_le_mul_of_nonneg_right hsp (mul_nonneg hz1.le hnn)
        _ = ((1 + z) * (1 + z) ^ ((1 : ℝ) / 2))
              * |Work.Spaces.mixed j i (E (fn n)) z θ| := by ring
    exact le_trans hmono (le_trans h1 (mul_le_mul_of_nonneg_left hBle hKpos.le))
  have h3 : |Work.Spaces.mixed j i (E (fn n)) z θ| ≤ K * max B 0 / (1 + z) := by
    rw [le_div_iff₀ hz1]
    calc |Work.Spaces.mixed j i (E (fn n)) z θ| * (1 + z)
        = (1 + z) * |Work.Spaces.mixed j i (E (fn n)) z θ| := by ring
      _ ≤ K * max B 0 := h2
  have hone : (1 : ℝ) ≤ 1 + 1 / z + 1 / (θ * (π / 2 - θ)) := by
    have hz' : 0 < 1 / z := by positivity
    have hθ' : 0 < 1 / (θ * (π / 2 - θ)) := by positivity
    linarith
  have hKB : 0 ≤ K * max B 0 := mul_nonneg hKpos.le hmaxnn
  calc |Work.Spaces.mixed j i (E (fn n)) z θ|
      ≤ K * max B 0 / (1 + z) := h3
    _ ≤ (K * max B 0 + 1) * (1 + 1 / z + 1 / (θ * (π / 2 - θ))) / (1 + z) := by
        rw [div_le_div_iff_of_pos_right hz1]
        nlinarith [hone, hKB]

/-! ## The obligation shapes over the repaired hypothesis

`Defs3.SmallLocalBound4` asks for the pointwise growth bounds along every `LimSeq4`, *for every
linear `E` carrying `HasPkg`*.  The `HasPkgD`-analogues below ask the same of every `E` carrying the
**repaired** packages; those are what the lead's field edit turns into the original shapes, and
they are what this area proves. -/

/-- **Obligation 1's first half over the repaired packages**: local growth bounds of order `≤ 4`
with the far-field rate `1/(1+z)`, along every `LimSeq4`, for every operator carrying `HasPkgD`. -/
def LocalBound4D (α Ce : ℝ) : Prop :=
  ∀ E : Fn →ₗ[ℝ] Fn, HasPkgD α Ce E → ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.mixed j i (E (fn n)) z θ|
        ≤ C * (1 + 1 / z + 1 / (θ * (π / 2 - θ))) / (1 + z)

/-- `LocalBound4D` is the `HasPkgD` form of the body of `Defs3.LocalBound4`. -/
theorem localBound4D_of_localBound4 {α Ce : ℝ} (h : LocalBound4 α Ce) : LocalBound4D α Ce :=
  fun E hE => h E hE.toHasPkg

/-- **The small-`α` obligation shape over the repaired packages.** -/
def SmallLocalBound4D : Prop :=
  ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ Ce : ℝ, LocalBound4D α Ce

/-- **`SmallLocalBound4D` holds** — this is the reduction `PkgRepair.localBound4_of_hasPkgD`,
packaged in the small-`α` shape (the obligation is only expected below a threshold, as for the
original `SmallLocalBound4`). -/
theorem smallLocalBound4D : SmallLocalBound4D :=
  ⟨1, one_pos, fun α hα _ Ce => localBound4_of_hasPkgD hα⟩

/-- **The decay clause of `Defs3.FatouData` over the repaired packages.**  This is the clause the
`PkgDecay` field is designed for: the relative form `≤ K·Xn6 α g` makes it uniform along a
`LimSeq4` (`LimSeq4.bound : Xn6 α (fn n) ≤ B`), so a single constant works for all `n`. -/
theorem fatouDecay_of_hasPkgD {α Ce : ℝ} (hα : 0 < α) :
    ∀ E : Fn →ₗ[ℝ] Fn, HasPkgD α Ce E → ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ,
        (z, θ) ∈ Work.Construction.Qd →
        (1 + z) ^ (3 / 2 : ℝ) * |Work.Spaces.mixed j i (E (fn n)) z θ| ≤ C := by
  intro E hE fn f hL
  obtain ⟨K, hKpos, hKD⟩ := hE.decay
  obtain ⟨B, hB⟩ := hL.bound
  refine ⟨K * max B 0 + 1, by positivity, ?_⟩
  intro n j i hji z θ hzθ
  have hji4 : j + i ≤ 4 := by omega
  have hBle : Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ max B 0 := le_trans (hB n) (le_max_left _ _)
  have h1 := hKD (fn n) (hL.classC n) j i hji4 z θ hzθ
  have h2 : (1 + z) ^ (3 / 2 : ℝ) * |Work.Spaces.mixed j i (E (fn n)) z θ| ≤ K * max B 0 :=
    le_trans h1 (mul_le_mul_of_nonneg_left hBle hKpos.le)
  linarith [h2]

/-! ## The two further primitive fields (the last two derivations)

`FatouData`'s remaining two clauses need data that no ℋ-membership supplies, and the review of
`phiTil_bundle_of_hasPkgD` pinned down exactly which two primitives are needed.  They are stated
here so that the two derivations can be done once and for all:

* `PkgCorner` — uniform (in `g`) bounds on the **plain iterated derivatives** of `E g` on every
  closed box.  `FatouData`'s `BoxData` clause consumes `BoxReg_of_uniform`, which asks for bounds
  on `iteratedFDeriv ℝ k` (`k ≤ 3`) on the box; the `mixed` normalisation of `PkgDecay` cannot give
  them, because `D_θ = sin(2θ)·∂_θ` degenerates at the corner (`BoxReg_of_uniform`'s conversion
  `∂_θ^i = D_θ^i/sin^i + lower` is 0/0 there).
* `PkgSlice` — uniform (in `z`) `θ`-slice bounds for the three slots.  `Defs3.ThetaBundle` demands
  `∀ z ∈ Iz, ∫_θ HkIntegrand α 0 Ψ z θ ≤ C`, a bound uniform in `z`, while every ℋ-membership is an
  integral *over* `z`; at the delicate end `z → 0` the weight is `≈ z^{-4}`.  Stating the primitive
  on the slots (where the packages already live) lets the `Φ̃`-level bounds follow by the same
  pointwise identities as `phiTil_bundle_of_hasPkgD`.
-/

/-- **The corner-regularity field**: uniform bounds on the plain iterated derivatives of `E g` on
every closed box — what `BoxReg_of_uniform` consumes. -/
def PkgCorner (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ g, Work.FTS.ClassC.ClassC α g →
    ∀ a b : ℝ, 0 < a → a ≤ b → ∀ k : ℕ, k ≤ 3 →
      ∀ p ∈ cbox a b,
        ‖iteratedFDeriv ℝ k (Function.uncurry (E g)) p‖ ≤ K * Work.FTS.StrongGlobal.Xn6 α g

/-- **The slice field**: uniform-in-`z` `θ`-slice bounds for the three packaged slots. -/
def PkgSlice (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ g, Work.FTS.ClassC.ClassC α g →
    ∀ (Φ : Fn), Φ = Work.Construction.PhiTil α g (E g) →
      (∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Work.Construction.Vop Φ) z θ) ≤
          K * Work.FTS.StrongGlobal.Xn6 α g) ∧
      (∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0
            (fun z θ => Work.Construction.Uop α Φ z θ / Work.Construction.s2 θ) z θ) ≤
          K * Work.FTS.StrongGlobal.Xn6 α g) ∧
      (∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun z θ => Work.Construction.PhiTil α g (E g) z θ / Real.cos θ) z θ) ≤
          K * Work.FTS.StrongGlobal.Xn6 α g) ∧
      (∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (Work.Spaces.mixed 0 1 (Work.Construction.Vop Φ)) z θ) ≤
          K * Work.FTS.StrongGlobal.Xn6 α g) ∧
      (∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (Work.Spaces.mixed 1 0
            (fun z θ => Work.Construction.Uop α Φ z θ / Work.Construction.s2 θ)) z θ) ≤
          K * Work.FTS.StrongGlobal.Xn6 α g)

/-- **The fully repaired hypothesis**: `HasPkgD` plus the two primitive fields above. -/
def HasPkgE (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  HasPkgD α Ce E ∧ PkgCorner α Ce E ∧ PkgSlice α Ce E

theorem HasPkgE.toHasPkgD {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgE α Ce E) :
    HasPkgD α Ce E := h.1

theorem HasPkgE.corner {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgE α Ce E) :
    PkgCorner α Ce E := h.2.1

theorem HasPkgE.slice {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgE α Ce E) :
    PkgSlice α Ce E := h.2.2

/-- **The last two obligation shapes over the fully repaired packages**, for the two remaining
derivations of `FatouData` (`ThetaBundle` and `BoxData`). -/
def ThetaBundleD (α Ce : ℝ) : Prop :=
  ∀ E : Fn →ₗ[ℝ] Fn, HasPkgE α Ce E → ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
    ∃ C : ℝ, 0 < C ∧
      (∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (Work.Construction.PhiTil α g (E g)) z θ) ≤ C) ∧
      (∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (Work.Spaces.pth (Work.Construction.PhiTil α g (E g))) z θ) ≤ C) ∧
      (∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (Work.Spaces.mixed 0 2 (Work.Construction.PhiTil α g (E g))) z θ) ≤ C) ∧
      (∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2
          * Work.Spaces.pzIter 2 (Work.Construction.PhiTil α g (E g)) z θ) z θ) ≤ C) ∧
      (∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun z θ => Work.Construction.PhiTil α g (E g) z θ / Real.cos θ) z θ) ≤ C)

def BoxDataD (α Ce : ℝ) : Prop :=
  ∀ E : Fn →ₗ[ℝ] Fn, HasPkgE α Ce E → ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∀ a b : ℝ, 0 < a → a ≤ b → ∃ G : Fn,
      ContDiffOn ℝ 2 (Function.uncurry G) (cbox a b) ∧
      (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
        Filter.Tendsto (fun n => E (fn n) z θ) Filter.atTop (𝓝 (G z θ))) ∧
      (∀ z ∈ Set.Icc a b, G z 0 = 0 ∧ G z (π / 2) = 0)

end Work.FTS_EllLimOK
