import Mathlib
import Submission.Work.DSM2b.FlatSetup
import Submission.Work.DSM2b.limit_kernel_range
import Submission.Work.DSM2b.assembly_aux
import Submission.Work.DSM2b.syzygy_helper
import Submission.Work.DSM2b.flat_mod_pow_v2

namespace Work.DSM2b

/-
**Bhatt, Prop. 4.1 (flat part).**  Let `R` be Noetherian, `π ∈ R` a nonzerodivisor, `B` an `R`-algebra
with `π` a nonzerodivisor on `B`, `B` `π`-adically complete, and `R/π → B/πB` flat.  Then `R → B`
is flat.  (This is the crux of the frozen node `DSMap.Mix.area_M2b`.)

**Proof strategy (verified by the area owner; every ingredient is available in Mathlib).**

Write `I = (a₁,…,a_l) ⊆ R` for a finitely generated ideal, `a : R^l → R`, `x ↦ Σ aᵢxᵢ` for a
surjection onto it, `S := ker a ⊆ R^l`, and fix a surjection `ρ : R^t ↠ S` with `S₂ := ker ρ ⊆ R^t`.
By `Module.Flat.iff_lift_lsmul_comp_subtype_injective` it suffices to show
`ker a_B = B·S := image(S ⊗[R] B → B^l)` for every such `I`: then `I ⊗[R] B = B^l / B·S → B` is
injective.

*(1) Flatness mod `π^M`.*  `B/π^M B` is flat over `R/π^M` for every `M` (dévissage along the
square-zero extensions `R/π^M ↠ R/π^{M-1}`, using `IsSMulRegular B π`; the sibling path
`Submission/Work/DSM2b/flat_mod_pow_of_flat_mod_base` does exactly this and may be imported or
inlined).  Hence, by exactness of `· ⊗ (B/π^M B)`, for **any** surjection `f : R^k ↠ N`:
`ker(N ⊗ (B/π^M B) ← (B/π^M B)^k) = image(ker f ⊗ (B/π^M B) → (B/π^M B)^k)`.

*(2) Artin–Rees.*  Mathlib has the Rees result for finitely generated modules over Noetherian
rings (`Ideal.exists_pow_inf_eq_pow_smul` and friends): for the finitely generated submodules
`I ⊆ R` and `S ⊆ R^l` there are `c, c'` with `I ∩ π^M R ⊆ π^{M-c} I` and
`S ∩ π^M R^l ⊆ π^{M-c'} S` for `M ≥ c, c'`.

*(3) Mod-`π^M` syzygies.*  Combining (1) and (2): with `S^{(M)} := ker(a mod π^M) ⊆ (R/π^M)^l`
one has `S^{(M)} ⊆ image(S) + π^{M-c}(R/π^M)^l` (lift `x̄` to `x` with `a x ∈ I ∩ π^M R ⊆ π^{M-c}I`,
write `a x = π^{M-c} w` with `w ∈ I`, lift `w` along `a`, subtract).  Consequently
`ker(a mod π^M) ⊆ (B·S + π^{M-c}B^l)/π^M B^l`; the identical argument with `ρ, S₂` gives
`ker(ρ mod π^M) ⊆ (B·S₂ + π^{M-c'}B^t)/π^M B^t`.

*(4) The limit.*  `B^l = lim_M (B/π^M B)^l` (`B` is `π`-adically complete, i.e. `IsHausdorff` +
`IsPrecomplete`), so for `u ∈ ker a_B`: `u ∈ B·S + π^{N}B^l` for every `N ≥ 1` (shift the index in
(3)).  Choose `β_M ∈ B^t` with `u - ρ_B(β_M) ∈ π^M B^l`.  Then
`ρ_B(β_{M+1} - β_M) ∈ π^M B^l`, so `β_{M+1} - β_M = σ_M + π^{M-c'}w_M` with `σ_M ∈ B·S₂` by (3);
put `β'_1 := β_1`, `β'_{M+1} := β'_M + (β_{M+1} - β_M) - σ_M`.  Then `ρ_B(β'_M) = ρ_B(β_M)` and
`β'_{M+1} ≡ β'_M mod π^{M-c'}B^t`, so `(β'_M)` converges (`IsPrecomplete.prec`) to some `β' ∈ B^t`,
and `ρ_B(β') = lim ρ_B(β'_M) = lim ρ_B(β_M) = u` because `u - ρ_B(β_M) ∈ π^MB^l` and `IsHausdorff`
kills the intersection.  Hence `u ∈ B·S`.  QED

(The `π`-adic completeness of `R` is *not* needed: step (3) uses only Noetherianness of `R`.)
-/
universe u

theorem flat_of_flat_mod_base {R B : Type u} [CommRing R] [IsNoetherianRing R] (π : R)
    (hπ : IsSMulRegular R π) [CommRing B] [Algebra R B]
    (hBπ : IsSMulRegular B (algebraMap R B π))
    [IsAdicComplete (Ideal.span {algebraMap R B π}) B]
    (h : Module.Flat (R ⧸ Ideal.span {π}) (B ⧸ (Ideal.span {π}).map (algebraMap R B))) :
    Module.Flat R B :=
  flat_of_flat_mod_base_aux π hBπ
    (fun n => flat_mod_pow_v2 π hπ hBπ h n)
    (fun g => exists_pow_sub_mem_ker_aux π g)
    (fun g c hc hflat n y hy => syzygy_mod_pow_helper π hflat g c hc n hy)

end Work.DSM2b
