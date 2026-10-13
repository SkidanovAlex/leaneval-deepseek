import Mathlib
import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5b.Basic
import Submission.Work.DSPB5.isAlmostZeroAlong_of_pow_mul_eq_zero

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open Opposite Limits
open scoped Simplicial
universe a

/-- The `b`-th component of a `Pi.lift` into a product in `ModuleCat`, evaluated at an element:
this is `Pi.lift_comp_π` read at the level of elements.  Stated abstractly so that no unfolding of
the concrete Čech complex is needed when it is applied. -/
lemma pi_lift_apply_π {M : Type*} [Ring M] {β : Type*} {f : β → ModuleCat M} [HasProduct f]
    {P : ModuleCat M} (p : (b : β) → P ⟶ f b) (b : β) (x : ↥P) :
    (Pi.π f b).hom ((Pi.lift p).hom x) = (p b).hom x := by
  rw [← ModuleCat.comp_apply, Pi.lift_comp_π]

/- The proof below rewrites the coaugmentation (a `Pi.lift` into the degree `0` term of a Čech
complex) against terms whose definitional equality with the Čech complex requires unfolding the
presheaf `perfChartPresheaf`; the type-correctness checks performed by `rw` then need the
transparency setting below to succeed. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- **M5b, almost injectivity of the coaugmentation.** `R → ∏_i R[J/t_i]^{1/p^∞}` has
`ϖ k = T^(1/p^k)`-torsion kernel for every `k`: if an element of `R` maps to `0` in every perfected
chart of the blowup of `Spec R` along `J = (t_i)`, then each `p`-power root of `T` annihilates it.
Route: the components of the coaugmentation are the localisation maps to `Localization.Away (t i)`,
so `w` is `t_i`-power torsion for every `i` (in particular at `i = j₀`, where `t j₀ = T^e`); hence
`T^N * w = 0` for some `N`; finally in a perfect ring `T^N * w = 0` implies `(T^(1/p^k)) * w = 0`
for all `k` (perfect ⇒ reduced; use `Work.DSPB5.isAlmostZeroAlong_of_pow_mul_eq_zero` or
`DSMap.Mix.isAlmostZeroAlong_of_mul_eq_zero` from `Submission/Work/DSPB5/`; note
`Work.DSPB5.pthRootPow p R k T` is definitionally `(frobeniusEquiv R p).symm^[k] T`).

Do NOT use the frozen sorried declaration `DSMap.Mix2.area_M5b`, nor any declaration of the
frozen `Submission/Work/DSMap/*.lean` whose proof is a `sorry`. -/
theorem perfChartCoaug_kernel (p : ℕ) [Fact p.Prime] (R : Type a) [CommRing R] [CharP R p]
    [PerfectRing R p] {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R) (T : R) (j₀ : ι) (e : ℕ)
    (hj₀ : t j₀ = T ^ e) (w : R) (hw : (perfChartCoaug p t).hom w = 0) (k : ℕ) :
    (frobeniusEquiv R p).symm^[k] T * w = 0 := by
  -- The `0`-simplex of the Čech nerve at which we read the component of the coaugmentation.
  set x : ToType ⦋0⦌ → ι := fun _ => j₀ with hx
  -- The `0`-th term of the Čech complex is the product over the `0`-simplices.
  let E0 := (FormalCoproduct.mk ι (chartIdx ι)).cech.obj (op ⦋0⦌)
  -- The chart through `x` is the chart `D₊(t_{j₀})` of the blowup: its defining product of
  -- `chartIdx ι` over `Fin 1` has underlying finset `{j₀}`.
  set S : Finset ι := (∏ᶜ (fun a : ToType ⦋0⦌ => chartIdx ι (x a))).unop with hS
  have hsub1 : ({j₀} : Finset ι) ≤ S := by
    have h := leOfHom (Pi.π (fun a : ToType ⦋0⦌ => chartIdx ι (x a)) (default : ToType ⦋0⦌)).unop
    simpa [hS, chartIdx, hx] using h
  have hsub2 : S ≤ ({j₀} : Finset ι) := by
    have h := leOfHom (Pi.lift (f := fun b : ToType ⦋0⦌ => chartIdx ι (x b))
      (fun _ => 𝟙 (chartIdx ι j₀))).unop
    simpa [hS, chartIdx, hx] using h
  have hSeq : S = {j₀} := le_antisymm hsub2 hsub1
  have htS : tS t S = t j₀ := by rw [hSeq]; simp [tS]
  -- The perfected chart ring, as a family over the `0`-simplices.
  let fam : (E0).I → ModuleCat R := fun y => ModuleCat.of R ↥(perfChartRing p t ((E0).obj y).unop)
  have hpc : (perfChartCoaug p t).hom w =
      (Pi.lift (fun y : (E0).I =>
        ModuleCat.ofHom (Algebra.linearMap R ↥(perfChartRing p t ((E0).obj y).unop)))).hom w := rfl
  -- The component of the coaugmentation at `x` is the structure map into the chart ring of `x`.
  have key : (Pi.π fam x).hom ((perfChartCoaug p t).hom w) = algebraMap R ↥(perfChartRing p t S) w := by
    rw [hpc]
    exact pi_lift_apply_π (M := R) (f := fam)
      (p := fun y : (E0).I => ModuleCat.ofHom (Algebra.linearMap R ↥(perfChartRing p t ((E0).obj y).unop))) x w
  have h2 : algebraMap R ↥(perfChartRing p t S) w = 0 := by
    calc algebraMap R ↥(perfChartRing p t S) w
        = (Pi.π fam x).hom ((perfChartCoaug p t).hom w) := key.symm
      _ = (Pi.π fam x).hom 0 := congrArg (fun z => (Pi.π fam x).hom z) hw
      _ = 0 := map_zero _
  -- The chart ring sits inside the localisation `R_{t_{j₀}}`, so `w` dies there.
  have h3 : algebraMap R (Localization.Away (tS t S)) w = 0 := by
    have := congrArg (fun z : ↥(perfChartRing p t S) => (z : Localization.Away (tS t S))) h2
    simpa [Subalgebra.coe_algebraMap] using this
  -- hence `w` is `t_{j₀}`-power torsion
  obtain ⟨n, hn⟩ : ∃ n, (tS t S) ^ n * w = 0 := by
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (tS t S))
      (Localization.Away (tS t S)) w).mp h3
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (m : R) (tS t S)).mp m.2
    exact ⟨n, by rw [hn]; exact hm⟩
  have hn' : (t j₀) ^ n * w = 0 := by rwa [htS] at hn
  have hn'' : (T ^ e) ^ n * w = 0 := by rwa [hj₀] at hn'
  have hTN : T ^ (e * n) * w = 0 := by rwa [← pow_mul] at hn''
  -- and `t^N`-torsion is almost zero along the tower of `p`-power roots of `t` in a perfect ring
  exact (Work.DSPB5.isAlmostZeroAlong_of_pow_mul_eq_zero p R T w (e * n) hTN) k

end Work.DSM5b
