import Mathlib
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SpecLin.Core.linEquiv_of_sections
import Submission.Work.SpecLin.Core.linEquiv_of_sections_of_chart
import Submission.Work.SpecLin.Alt.chartMap
import Submission.Work.SpecLin.Alt.chartReading
import Submission.Work.SpecLin.Alt.conservationNumber
import Submission.Work.SpecLin.Alt.exists_chartTensorPoint
import Submission.Work.SpecLin.Alt.exists_chartTensorFibrePoint
import Submission.Work.SpecLin.Alt.sectionPrime_le_iff_ptPlace_eq_alt
import Submission.Work.SpecLin.Alt.sectionPrime_le_iff_ptPlace_eq_residue
import Submission.Work.SpecLin.Alt.ordAt_chartTensorRedMap_eq_one
import Submission.Work.SpecLin.Alt.ordAt_chartTensorRedMap_eq_zero_iff_isUnit
import Submission.Work.SpecLin.Alt.exists_normalized_chartTensorMap
import Submission.Work.SpecLin.Core.section_prime_sup_fibre_quot
import Submission.Work.CurveBasics.Basic
import Submission.Work.SpecLin.Setup.localOrderData
import Submission.Work.SpecLin.Setup.localOrderHmiss
import Submission.Work.SpecLin.Setup.localOrderUniformizer

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SpecLin.Setup

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

set_option maxHeartbeats 8000000

/-- **The local reading-off at a closed point of the special fibre.**

In the relative chart `B = Γ(C,W) ⊗[K] R` (with fibre prime `P = chartFibrePrime R W`), let
`h' ∈ K(C_F)^×` satisfy `div h' = Σ_m [s_m^F] − Σ_m [t_m^F]` (`hdiv`) and let `a, b ∈ B ∖ P` with
`h' * φ b = φ a`, `φ = chartTensorMap R W hW`.  Let `N ⊇ P` be a maximal ideal, `z` the
corresponding closed point of the special fibre (the order dictionary `hz`), and for every `m` let
`f m ∈ I_m = sectionPrime` (resp. `g m ∈ J_m`) generate `I_m` (resp. `J_m`) locally at `N`, with
`f m, g m ∉ P` and the unit criterion at every prime `p ≤ N` (`eqS`, `eqT`; these are the
conclusions of `Work.SpecLin.Setup.sectionEquationPull`).

If moreover `cruxAt` holds — every `v ∈ Frac B`, `v ≠ 0`, which is a unit at `P` and at every
height-one prime `p ≤ N` is a unit at `N` (this is `Work.SpecLin.Setup.cruxChartPull`, resp.
`Setup.cruxPITdomain`) — then the order at `z` of the reduction of `h' = a/b` is the difference
of the numbers of sections through `z`:

  `ord_z(ρ a / ρ b) = #{m : I_m ⊔ P = N} − #{m : J_m ⊔ P = N}`.

The proof: put `u = (a/b)·Π g_m/Π f_m ∈ Frac B`.  `u` is a unit at `P` (product of elements
outside `P`, `Alt.isUnitAt_chartFibrePrime_of_map_mul_eq`), and it is a unit at every height-one
prime `p ≤ N`: for `p ⊆ P` this is `Alt.isUnitAt_of_le_chartFibrePrime`; for `p ⊄ P` height-one
one has `p ∩ R = 0`, hence `p` corresponds to a place `Q` of `C_F` (`Alt.exists_chartTensorPoint`)
and `ord_Q(h') = #{m : I_m ≤ p} − #{m : J_m ≤ p}` (`Alt.ordAt_of_div_eq_sum_ptDiv` together with
the section dictionary `Alt.sectionPrime_le_iff_ptPlace_eq_alt`), while
`ord_p(f m) = [I_m ≤ p]` (`eqS`).  So `cruxAt` gives `IsUnitAt u N`; writing `u = p/q` with
`p, q ∈ B` units of `B_N` makes `a·(Π g_m)·q = b·(Π f_m)·p`, and
`Alt.div_chartTensorRedMap_div_apply` concludes. -/
theorem localOrderPull {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    [IsDomain (Work.SpecLin.Core.chartTensor R W)]
    (s t : Fin n → Work.SpecLin.CurvePt C R)
    (hs : ∀ m, Set.range (s m).left.base ⊆ (W : Set C.left))
    (ht : ∀ m, Set.range (t m).left.base ⊆ (W : Set C.left))
    (h' : (C.baseChange (FractionRing R)).functionField) (hh' : h' ≠ 0)
    (hdiv : (C.baseChange (FractionRing R)).div h'
      = (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
          (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (s m)))
        - (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv
          (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) (t m))))
    (a b : Work.SpecLin.Core.chartTensor R W)
    (ha : a ∉ Work.SpecLin.Core.chartFibrePrime R W)
    (hb : b ∉ Work.SpecLin.Core.chartFibrePrime R W)
    (hab : h' * Work.SpecLin.Alt.chartTensorMap R W hW b
        = Work.SpecLin.Alt.chartTensorMap R W hW a)
    (N : Ideal (Work.SpecLin.Core.chartTensor R W)) (hN : N.IsMaximal)
    (hPN : Work.SpecLin.Core.chartFibrePrime R W ≤ N)
    (eqS : ∀ m : Fin n, ∃ f : Work.SpecLin.Core.chartTensor R W,
      f ∈ Work.SpecLin.Core.sectionPrime R W (Work.SpecLin.Core.rgMap R W hW (s m) (hs m)) ∧
      f ∉ Work.SpecLin.Core.chartFibrePrime R W ∧
      (Work.SpecLin.Core.sectionPrime R W (Work.SpecLin.Core.rgMap R W hW (s m) (hs m))).map
        (algebraMap (Work.SpecLin.Core.chartTensor R W) (Localization.AtPrime N))
        = Ideal.span (singleton (algebraMap (Work.SpecLin.Core.chartTensor R W)
            (Localization.AtPrime N) f)) ∧
      (∀ p : Ideal (Work.SpecLin.Core.chartTensor R W), p.IsPrime → p ≤ N →
        (Work.SpecLin.Alt.IsUnitAt (algebraMap (Work.SpecLin.Core.chartTensor R W)
            (FractionRing (Work.SpecLin.Core.chartTensor R W)) f) p
          ↔ ¬ (Work.SpecLin.Core.sectionPrime R W
                (Work.SpecLin.Core.rgMap R W hW (s m) (hs m)) ≤ p))))
    (eqT : ∀ m : Fin n, ∃ f : Work.SpecLin.Core.chartTensor R W,
      f ∈ Work.SpecLin.Core.sectionPrime R W (Work.SpecLin.Core.rgMap R W hW (t m) (ht m)) ∧
      f ∉ Work.SpecLin.Core.chartFibrePrime R W ∧
      (Work.SpecLin.Core.sectionPrime R W (Work.SpecLin.Core.rgMap R W hW (t m) (ht m))).map
        (algebraMap (Work.SpecLin.Core.chartTensor R W) (Localization.AtPrime N))
        = Ideal.span (singleton (algebraMap (Work.SpecLin.Core.chartTensor R W)
            (Localization.AtPrime N) f)) ∧
      (∀ p : Ideal (Work.SpecLin.Core.chartTensor R W), p.IsPrime → p ≤ N →
        (Work.SpecLin.Alt.IsUnitAt (algebraMap (Work.SpecLin.Core.chartTensor R W)
            (FractionRing (Work.SpecLin.Core.chartTensor R W)) f) p
          ↔ ¬ (Work.SpecLin.Core.sectionPrime R W
                (Work.SpecLin.Core.rgMap R W hW (t m) (ht m)) ≤ p))))
    (cruxAt : ∀ v : FractionRing (Work.SpecLin.Core.chartTensor R W), v ≠ 0 →
      Work.SpecLin.Alt.IsUnitAt v (Work.SpecLin.Core.chartFibrePrime R W) →
      (∀ p : Ideal (Work.SpecLin.Core.chartTensor R W), p.IsPrime → p.height = 1 → p ≤ N →
        Work.SpecLin.Alt.IsUnitAt v p) →
      Work.SpecLin.Alt.IsUnitAt v N)
    (z : (C.baseChange (IsLocalRing.ResidueField R)).Place)
    (hz : ∀ x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
      (∃ a b : Work.SpecLin.Core.chartTensor R W, b ∉ N ∧
          x * Work.SpecLin.Alt.chartTensorRedMap R W hW b
            = Work.SpecLin.Alt.chartTensorRedMap R W hW a)
        ↔ 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z) :
    (C.baseChange (IsLocalRing.ResidueField R)).ordAt
        (Work.SpecLin.Alt.chartTensorRedMap R W hW a
          * (Work.SpecLin.Alt.chartTensorRedMap R W hW b)⁻¹) z
      = ((Finset.univ.filter (fun m : Fin n => Work.SpecLin.Core.sectionPrime R W
              (Work.SpecLin.Core.rgMap R W hW (s m) (hs m)) ⊔
                Work.SpecLin.Core.chartFibrePrime R W = N)).card : ℤ)
        - ((Finset.univ.filter (fun m : Fin n => Work.SpecLin.Core.sectionPrime R W
              (Work.SpecLin.Core.rgMap R W hW (t m) (ht m)) ⊔
                Work.SpecLin.Core.chartFibrePrime R W = N)).card : ℤ) := by
  classical
  haveI hNmax : N.IsMaximal := hN
  haveI hNp : N.IsPrime := hN.isPrime
  have hPp : (Work.SpecLin.Core.chartFibrePrime R W).IsPrime :=
    Work.SpecLin.Core.isPrime_chartFibrePrime R W hW
  -- ## The local equations of the section ideals at `N`
  choose f hfmem hfP hfgen hfunit using eqS
  choose g hgmem hgP hggen hgunit using eqT
  have hf0 : ∀ m : Fin n, f m ≠ 0 := fun m h => hfP m (by rw [h]; exact Ideal.zero_mem _)
  have hg0 : ∀ m : Fin n, g m ≠ 0 := fun m h => hgP m (by rw [h]; exact Ideal.zero_mem _)
  -- ## The numerator, the denominator and the element `U = num / den`
  set num : Work.SpecLin.Core.chartTensor R W := a * ∏ m, g m with hnumdef
  set den : Work.SpecLin.Core.chartTensor R W := b * ∏ m, f m with hdendef
  have hprodgP : (∏ m : Fin n, g m) ∉ Work.SpecLin.Core.chartFibrePrime R W := by
    refine Finset.prod_induction g
      (fun x => x ∉ Work.SpecLin.Core.chartFibrePrime R W) ?_ ?_ ?_
    · intro x y hx hy hxy
      rcases (Ideal.IsPrime.mul_mem_iff_mem_or_mem hPp).mp hxy with h | h
      · exact hx h
      · exact hy h
    · intro h; exact hPp.ne_top (Ideal.eq_top_iff_one _ |>.mpr h)
    · intro m _; exact hgP m
  have hprodfP : (∏ m : Fin n, f m) ∉ Work.SpecLin.Core.chartFibrePrime R W := by
    refine Finset.prod_induction f
      (fun x => x ∉ Work.SpecLin.Core.chartFibrePrime R W) ?_ ?_ ?_
    · intro x y hx hy hxy
      rcases (Ideal.IsPrime.mul_mem_iff_mem_or_mem hPp).mp hxy with h | h
      · exact hx h
      · exact hy h
    · intro h; exact hPp.ne_top (Ideal.eq_top_iff_one _ |>.mpr h)
    · intro m _; exact hfP m
  have hnumP : num ∉ Work.SpecLin.Core.chartFibrePrime R W := by
    rw [hnumdef]
    intro h
    rcases (Ideal.IsPrime.mul_mem_iff_mem_or_mem hPp).mp h with h | h
    · exact ha h
    · exact hprodgP h
  have hdenP : den ∉ Work.SpecLin.Core.chartFibrePrime R W := by
    rw [hdendef]
    intro h
    rcases (Ideal.IsPrime.mul_mem_iff_mem_or_mem hPp).mp h with h | h
    · exact hb h
    · exact hprodfP h
  have hnum0 : num ≠ 0 := fun h => hnumP (by rw [h]; exact Ideal.zero_mem _)
  have hden0 : den ≠ 0 := fun h => hdenP (by rw [h]; exact Ideal.zero_mem _)
  let U : FractionRing (Work.SpecLin.Core.chartTensor R W) :=
    algebraMap _ _ num * (algebraMap _ _ den)⁻¹
  have hU : algebraMap (Work.SpecLin.Core.chartTensor R W)
      (FractionRing (Work.SpecLin.Core.chartTensor R W)) num
      = U * algebraMap (Work.SpecLin.Core.chartTensor R W)
          (FractionRing (Work.SpecLin.Core.chartTensor R W)) den := by
    show algebraMap _ _ num
      = (algebraMap _ _ num * (algebraMap _ _ den)⁻¹) * algebraMap _ _ den
    rw [mul_assoc, inv_mul_cancel₀, mul_one]
    intro h
    exact hden0 (IsFractionRing.injective _ _ (by rw [h, map_zero]))
  have hU0 : U ≠ 0 := by
    intro h0
    have h1 : algebraMap (Work.SpecLin.Core.chartTensor R W)
        (FractionRing (Work.SpecLin.Core.chartTensor R W)) num
        = (0 : FractionRing (Work.SpecLin.Core.chartTensor R W)) := by
      rw [hU, h0, zero_mul]
    exact hnum0 (IsFractionRing.injective _ _ (by rw [h1, map_zero]))
  -- ## `U` is a unit at the fibre prime
  have hUP : Work.SpecLin.Alt.IsUnitAt U (Work.SpecLin.Core.chartFibrePrime R W) :=
    Work.SpecLin.Alt.isUnitAt_chartFibrePrime_of_map_mul_eq R W num den hnumP hdenP U hU
  -- ## `U` is a unit at every height-one prime `p ≤ N`
  have hht : ∀ p : Ideal (Work.SpecLin.Core.chartTensor R W), p.IsPrime → p.height = 1 →
      p ≤ N → Work.SpecLin.Alt.IsUnitAt U p := by
    intro p hp hp1 hpN
    by_cases hpP : p ≤ Work.SpecLin.Core.chartFibrePrime R W
    · exact Work.SpecLin.Alt.isUnitAt_of_le_chartFibrePrime R W U p hpP hUP
    · haveI hpI : p.IsPrime := hp
      have hmiss := Work.SpecLin.Setup.localOrderHmiss R W hW p hp hp1 hpP
      obtain ⟨Q, hQmem, hQdict⟩ :=
        Work.SpecLin.Alt.exists_chartTensorPoint R W hW p hp hp1 hmiss
      -- the section dictionary
      have hIp : ∀ m : Fin n, Work.SpecLin.Core.sectionPrime R W
            (Work.SpecLin.Core.rgMap R W hW (s m) (hs m)) ≤ p
          ↔ Work.SpecLin.ptPlace (Work.SpecLin.RPt.map
              (IsScalarTower.toAlgHom K R (FractionRing R)) (s m)) = Q :=
        fun m => Work.SpecLin.Alt.sectionPrime_le_iff_ptPlace_eq_alt R W hW
          (s m) (hs m) p hp hmiss Q hQmem hQdict
      have hJp : ∀ m : Fin n, Work.SpecLin.Core.sectionPrime R W
            (Work.SpecLin.Core.rgMap R W hW (t m) (ht m)) ≤ p
          ↔ Work.SpecLin.ptPlace (Work.SpecLin.RPt.map
              (IsScalarTower.toAlgHom K R (FractionRing R)) (t m)) = Q :=
        fun m => Work.SpecLin.Alt.sectionPrime_le_iff_ptPlace_eq_alt R W hW
          (t m) (ht m) p hp hmiss Q hQmem hQdict
      have hcount : (C.baseChange (FractionRing R)).ordAt h' Q
          = ((Finset.univ.filter (fun m : Fin n => Work.SpecLin.Core.sectionPrime R W
                (Work.SpecLin.Core.rgMap R W hW (s m) (hs m)) ≤ p)).card : ℤ)
            - ((Finset.univ.filter (fun m : Fin n => Work.SpecLin.Core.sectionPrime R W
                (Work.SpecLin.Core.rgMap R W hW (t m) (ht m)) ≤ p)).card : ℤ) :=
        Work.SpecLin.Alt.ordAt_of_div_eq_sum_ptDiv R W hW s t hs ht Q p hQdict hIp hJp h' hdiv
      have hφinj : Function.Injective (Work.SpecLin.Alt.chartTensorMap R W hW) := by
        letI : Algebra (Work.SpecLin.Core.chartTensor R W)
            (C.baseChange (FractionRing R)).functionField :=
          (Work.SpecLin.Alt.chartTensorMap R W hW).toAlgebra
        haveI : IsFractionRing (Work.SpecLin.Core.chartTensor R W)
            (C.baseChange (FractionRing R)).functionField :=
          Work.SpecLin.Alt.chartTensorMap_isFractionRing R W hW
        exact IsFractionRing.injective _ _
      have hφb0 : Work.SpecLin.Alt.chartTensorMap R W hW b ≠ 0 := fun h =>
        (fun hb0 : b = 0 => hb (by rw [hb0]; exact Ideal.zero_mem _))
          (hφinj (by rw [h, map_zero]))
      -- orders of the local equations
      have hford : ∀ m : Fin n, (C.baseChange (FractionRing R)).ordAt
          (Work.SpecLin.Alt.chartTensorMap R W hW (f m)) Q
          = if Work.SpecLin.Core.sectionPrime R W
                (Work.SpecLin.Core.rgMap R W hW (s m) (hs m)) ≤ p then 1 else 0 := by
        intro m
        by_cases hm : Work.SpecLin.Core.sectionPrime R W
            (Work.SpecLin.Core.rgMap R W hW (s m) (hs m)) ≤ p
        · rw [if_pos hm]
          haveI hIprime : (Work.SpecLin.Core.sectionPrime R W
              (Work.SpecLin.Core.rgMap R W hW (s m) (hs m))).IsPrime :=
            Work.SpecLin.Core.isPrime_sectionPrime R W (Work.SpecLin.Core.rgMap R W hW (s m) (hs m))
          have hIm_ne : Work.SpecLin.Core.sectionPrime R W
              (Work.SpecLin.Core.rgMap R W hW (s m) (hs m)) ≠ ⊥ := by
            intro hbot
            exact hf0 m (Ideal.mem_bot.mp (hbot ▸ hfmem m))
          have hIm_eq : Work.SpecLin.Core.sectionPrime R W
              (Work.SpecLin.Core.rgMap R W hW (s m) (hs m)) = p := by
            rcases lt_or_eq_of_le hm with hlt | heq
            · exfalso
              have hle1 : p.height ≤ ((1 : ℕ) : ℕ∞) := by
                rw [hp1]; exact le_of_eq (Nat.cast_one).symm
              have hlt2 := (Ideal.height_le_iff.mp hle1) _ hIprime hlt
              have h0 : (Work.SpecLin.Core.sectionPrime R W
                  (Work.SpecLin.Core.rgMap R W hW (s m) (hs m))).height = 0 := by
                by_contra hh
                have h1 : ((1 : ℕ) : ℕ∞) ≤ (Work.SpecLin.Core.sectionPrime R W
                    (Work.SpecLin.Core.rgMap R W hW (s m) (hs m))).height := by
                  rw [Nat.cast_one]
                  exact Order.one_le_iff_ne_zero.mpr hh
                exact not_le.mpr hlt2 h1
              exact hIm_ne (Ideal.height_eq_zero_iff_eq_bot.mp h0)
            · exact heq
          have hf : Ideal.span ((singleton (algebraMap (Work.SpecLin.Core.chartTensor R W)
                (Localization.AtPrime p) (f m))) : Set (Localization.AtPrime p))
              = IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
            have hmap := Work.SpecLin.Setup.ideal_map_atPrime_le N p hpN
              (Work.SpecLin.Core.sectionPrime R W (Work.SpecLin.Core.rgMap R W hW (s m) (hs m)))
              (f m) (hfgen m)
            rw [hIm_eq, IsLocalization.AtPrime.map_eq_maximalIdeal p
              (Localization.AtPrime p)] at hmap
            exact hmap.symm
          exact Work.SpecLin.Setup.localOrderUniformizer R W hW p Q hQdict (f m) hf
        · rw [if_neg hm]
          have hunit : Work.SpecLin.Alt.IsUnitAt
              (algebraMap (Work.SpecLin.Core.chartTensor R W)
                (FractionRing (Work.SpecLin.Core.chartTensor R W)) (f m)) p :=
            (hfunit m p hp hpN).mpr hm
          have hne : algebraMap (Work.SpecLin.Core.chartTensor R W)
              (FractionRing (Work.SpecLin.Core.chartTensor R W)) (f m) ≠ 0 := fun h =>
            hf0 m (IsFractionRing.injective _ _ (by rw [h, map_zero]))
          have h2 := (Work.SpecLin.Setup.isUnitAt_iff_ordAt_eq_zero R W hW p Q hQdict _ hne).mp hunit
          rwa [chartTensorFracMap_algebraMap] at h2
      have hgord : ∀ m : Fin n, (C.baseChange (FractionRing R)).ordAt
          (Work.SpecLin.Alt.chartTensorMap R W hW (g m)) Q
          = if Work.SpecLin.Core.sectionPrime R W
                (Work.SpecLin.Core.rgMap R W hW (t m) (ht m)) ≤ p then 1 else 0 := by
        intro m
        by_cases hm : Work.SpecLin.Core.sectionPrime R W
            (Work.SpecLin.Core.rgMap R W hW (t m) (ht m)) ≤ p
        · rw [if_pos hm]
          haveI hIprime : (Work.SpecLin.Core.sectionPrime R W
              (Work.SpecLin.Core.rgMap R W hW (t m) (ht m))).IsPrime :=
            Work.SpecLin.Core.isPrime_sectionPrime R W (Work.SpecLin.Core.rgMap R W hW (t m) (ht m))
          have hIm_ne : Work.SpecLin.Core.sectionPrime R W
              (Work.SpecLin.Core.rgMap R W hW (t m) (ht m)) ≠ ⊥ := by
            intro hbot
            exact hg0 m (Ideal.mem_bot.mp (hbot ▸ hgmem m))
          have hIm_eq : Work.SpecLin.Core.sectionPrime R W
              (Work.SpecLin.Core.rgMap R W hW (t m) (ht m)) = p := by
            rcases lt_or_eq_of_le hm with hlt | heq
            · exfalso
              have hle1 : p.height ≤ ((1 : ℕ) : ℕ∞) := by
                rw [hp1]; exact le_of_eq (Nat.cast_one).symm
              have hlt2 := (Ideal.height_le_iff.mp hle1) _ hIprime hlt
              have h0 : (Work.SpecLin.Core.sectionPrime R W
                  (Work.SpecLin.Core.rgMap R W hW (t m) (ht m))).height = 0 := by
                by_contra hh
                have h1 : ((1 : ℕ) : ℕ∞) ≤ (Work.SpecLin.Core.sectionPrime R W
                    (Work.SpecLin.Core.rgMap R W hW (t m) (ht m))).height := by
                  rw [Nat.cast_one]
                  exact Order.one_le_iff_ne_zero.mpr hh
                exact not_le.mpr hlt2 h1
              exact hIm_ne (Ideal.height_eq_zero_iff_eq_bot.mp h0)
            · exact heq
          have hf : Ideal.span ((singleton (algebraMap (Work.SpecLin.Core.chartTensor R W)
                (Localization.AtPrime p) (g m))) : Set (Localization.AtPrime p))
              = IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
            have hmap := Work.SpecLin.Setup.ideal_map_atPrime_le N p hpN
              (Work.SpecLin.Core.sectionPrime R W (Work.SpecLin.Core.rgMap R W hW (t m) (ht m)))
              (g m) (hggen m)
            rw [hIm_eq, IsLocalization.AtPrime.map_eq_maximalIdeal p
              (Localization.AtPrime p)] at hmap
            exact hmap.symm
          exact Work.SpecLin.Setup.localOrderUniformizer R W hW p Q hQdict (g m) hf
        · rw [if_neg hm]
          have hunit : Work.SpecLin.Alt.IsUnitAt
              (algebraMap (Work.SpecLin.Core.chartTensor R W)
                (FractionRing (Work.SpecLin.Core.chartTensor R W)) (g m)) p :=
            (hgunit m p hp hpN).mpr hm
          have hne : algebraMap (Work.SpecLin.Core.chartTensor R W)
              (FractionRing (Work.SpecLin.Core.chartTensor R W)) (g m) ≠ 0 := fun h =>
            hg0 m (IsFractionRing.injective _ _ (by rw [h, map_zero]))
          have h2 := (Work.SpecLin.Setup.isUnitAt_iff_ordAt_eq_zero R W hW p Q hQdict _ hne).mp hunit
          rwa [chartTensorFracMap_algebraMap] at h2
      -- ## the order of `U` at `Q` vanishes
      refine (Work.SpecLin.Setup.isUnitAt_iff_ordAt_eq_zero R W hW p Q hQdict U hU0).mpr ?_
      have hΦU : chartTensorFracMap R W hW U
          = h' * (∏ m : Fin n, Work.SpecLin.Alt.chartTensorMap R W hW (g m))
            * (∏ m : Fin n, Work.SpecLin.Alt.chartTensorMap R W hW (f m))⁻¹ := by
        show chartTensorFracMap R W hW
            (algebraMap _ _ num * (algebraMap _ _ den)⁻¹) = _
        rw [map_mul, map_inv₀, chartTensorFracMap_algebraMap R W hW num,
          chartTensorFracMap_algebraMap R W hW den, hnumdef, hdendef, map_mul, map_mul,
          map_prod, map_prod, hab.symm]
        field_simp
      have hmapf0 : ∀ m : Fin n, Work.SpecLin.Alt.chartTensorMap R W hW (f m) ≠ 0 :=
        fun m h => hf0 m (hφinj (by rw [h, map_zero]))
      have hmapg0 : ∀ m : Fin n, Work.SpecLin.Alt.chartTensorMap R W hW (g m) ≠ 0 :=
        fun m h => hg0 m (hφinj (by rw [h, map_zero]))
      have hφf0 : (∏ m : Fin n, Work.SpecLin.Alt.chartTensorMap R W hW (f m)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun m _ => hmapf0 m)
      have hφg0 : (∏ m : Fin n, Work.SpecLin.Alt.chartTensorMap R W hW (g m)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun m _ => hmapg0 m)
      rw [hΦU]
      rw [Work.CurveBasics.Curve.ordAt_mul _ (mul_ne_zero hh' hφg0) (inv_ne_zero hφf0)]
      rw [Work.CurveBasics.Curve.ordAt_mul _ hh' hφg0]
      rw [Work.SpecLin.Alt.ordAt_prod (F := FractionRing R) _ _ _ (fun m _ => hmapg0 m) Q]
      rw [Work.CurveBasics.Curve.ordAt_inv _ hφf0]
      rw [Work.SpecLin.Alt.ordAt_prod (F := FractionRing R) _ _ _ (fun m _ => hmapf0 m) Q]
      rw [hcount]
      rw [Finset.sum_congr rfl (fun m _ => hford m),
        Finset.sum_congr rfl (fun m _ => hgord m)]
      have hcardI : ((Finset.univ.filter (fun m : Fin n => Work.SpecLin.Core.sectionPrime R W
            (Work.SpecLin.Core.rgMap R W hW (s m) (hs m)) ≤ p)).card : ℤ)
          = ∑ m : Fin n, (if Work.SpecLin.Core.sectionPrime R W
              (Work.SpecLin.Core.rgMap R W hW (s m) (hs m)) ≤ p then (1 : ℤ) else 0) := by
        rw [Finset.card_filter]; push_cast; rfl
      have hcardJ : ((Finset.univ.filter (fun m : Fin n => Work.SpecLin.Core.sectionPrime R W
            (Work.SpecLin.Core.rgMap R W hW (t m) (ht m)) ≤ p)).card : ℤ)
          = ∑ m : Fin n, (if Work.SpecLin.Core.sectionPrime R W
              (Work.SpecLin.Core.rgMap R W hW (t m) (ht m)) ≤ p then (1 : ℤ) else 0) := by
        rw [Finset.card_filter]; push_cast; rfl
      rw [hcardI, hcardJ]
      ring
  -- ## The crux
  have hUN : Work.SpecLin.Alt.IsUnitAt U N := cruxAt U hU0 hUP hht
  -- ## Write `U = pp / qq` with `pp, qq ∉ N`
  obtain ⟨pp, qq, hppN, hqqN, hUid⟩ :=
    Work.SpecLin.Setup.exists_notMem_of_isUnitAt N U hU0 hUN
  have hppP : pp ∉ Work.SpecLin.Core.chartFibrePrime R W := fun h => hppN (hPN h)
  have hqqP : qq ∉ Work.SpecLin.Core.chartFibrePrime R W := fun h => hqqN (hPN h)
  have hppU : IsUnit (algebraMap (Work.SpecLin.Core.chartTensor R W)
      (Localization.AtPrime N) pp) := by
    have hcompl : pp ∈ N.primeCompl := hppN
    exact IsLocalization.map_units (Localization.AtPrime N) ⟨pp, hcompl⟩
  have hqqU : IsUnit (algebraMap (Work.SpecLin.Core.chartTensor R W)
      (Localization.AtPrime N) qq) := by
    have hcompl : qq ∈ N.primeCompl := hqqN
    exact IsLocalization.map_units (Localization.AtPrime N) ⟨qq, hcompl⟩
  -- ## The cross-multiplication identity
  have hident : a * (∏ m : Fin n, g m) * qq = b * (∏ m : Fin n, f m) * pp := by
    have key : num * qq = den * pp := by
      refine IsFractionRing.injective (Work.SpecLin.Core.chartTensor R W)
        (FractionRing (Work.SpecLin.Core.chartTensor R W)) ?_
      calc algebraMap _ _ (num * qq)
          = (U * algebraMap _ _ den) * algebraMap _ _ qq := by rw [map_mul, hU]
        _ = algebraMap _ _ den * (U * algebraMap _ _ qq) := by ring
        _ = algebraMap _ _ den * algebraMap _ _ pp := by rw [hUid]
        _ = algebraMap _ _ (den * pp) := (map_mul _ _ _).symm
    rw [hnumdef, hdendef] at key
    exact key
  -- ## The reading-off on the special fibre
  have hmain := Work.SpecLin.Alt.ordAt_chartTensorRedMap_div_eq R W hW s t hs ht N hPN
    z hz a b pp qq ha hb hppP hqqP hppU hqqU f g hfP hgP hfgen hggen hident
  have hmain2 : (C.baseChange (IsLocalRing.ResidueField R)).div
        (Work.SpecLin.Alt.chartTensorRedMap R W hW a
          * (Work.SpecLin.Alt.chartTensorRedMap R W hW b)⁻¹) z
      = (∑ m : Fin n, if (Work.SpecLin.Core.sectionPrime R W
              (Work.SpecLin.Core.rgMap R W hW (s m) (hs m)) ⊔
                Work.SpecLin.Core.chartFibrePrime R W = N) then (1 : ℤ) else 0)
        - (∑ m : Fin n, if (Work.SpecLin.Core.sectionPrime R W
              (Work.SpecLin.Core.rgMap R W hW (t m) (ht m)) ⊔
                Work.SpecLin.Core.chartFibrePrime R W = N) then (1 : ℤ) else 0) := by
    rw [div_eq_mul_inv] at hmain
    exact hmain
  have hcardI : ((Finset.univ.filter (fun m : Fin n => Work.SpecLin.Core.sectionPrime R W
        (Work.SpecLin.Core.rgMap R W hW (s m) (hs m)) ⊔
          Work.SpecLin.Core.chartFibrePrime R W = N)).card : ℤ)
      = (∑ m : Fin n, if (Work.SpecLin.Core.sectionPrime R W
          (Work.SpecLin.Core.rgMap R W hW (s m) (hs m)) ⊔
            Work.SpecLin.Core.chartFibrePrime R W = N) then (1 : ℤ) else 0) := by
    rw [Finset.card_filter]; push_cast; rfl
  have hcardJ : ((Finset.univ.filter (fun m : Fin n => Work.SpecLin.Core.sectionPrime R W
        (Work.SpecLin.Core.rgMap R W hW (t m) (ht m)) ⊔
          Work.SpecLin.Core.chartFibrePrime R W = N)).card : ℤ)
      = (∑ m : Fin n, if (Work.SpecLin.Core.sectionPrime R W
          (Work.SpecLin.Core.rgMap R W hW (t m) (ht m)) ⊔
            Work.SpecLin.Core.chartFibrePrime R W = N) then (1 : ℤ) else 0) := by
    rw [Finset.card_filter]; push_cast; rfl
  rw [hcardI, hcardJ, ← hmain2]
  exact (Work.CurveBasics.Curve.div_apply (C.baseChange (IsLocalRing.ResidueField R))
    (Work.SpecLin.Alt.chartTensorRedMap R W hW a
      * (Work.SpecLin.Alt.chartTensorRedMap R W hW b)⁻¹) z).symm

end Work.SpecLin.Setup
