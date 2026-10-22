import Mathlib
import Submission.Work.TOOLKIT.SeqColim.Defs

open CategoryTheory Limits

namespace Work.TOOLKIT.SeqColim

/-! ## The telescope cocone attached to a point with `telD F ≫ k = 0`

Given a morphism `k : ∐_n F.obj n ⟶ A` which is killed by `telD F = 1 - shift`, the maps
`n ↦ Sigma.ι _ n ≫ k` form a cocone over `F`, hence descend to a map `colim F ⟶ A`. -/

/-- The single-step computation: since `telD F ≫ k = 0`, the `n`-th component of `k` equals the
`(n+1)`-st component precomposed with the `n`-th transition map.  This is the identity
`Sigma_ι_towerD` for `X := fun n => F.obj n` and `i := step F`, applied to `k`. -/
lemma step_ι_comp (F : ℕ ⥤ Cpx) {A : Cpx} (k : (∐ fun n => F.obj n) ⟶ A)
    (hk : telD F ≫ k = 0) (n : ℕ) :
    step F n ≫ (Sigma.ι (fun n => F.obj n) (n+1) ≫ k) = Sigma.ι (fun n => F.obj n) n ≫ k := by
  have h := congrArg (fun w => w ≫ k) (Sigma_ι_towerD (fun n => F.obj n) (step F) n)
  rw [show towerD (fun n => F.obj n) (step F) = telD F from rfl,
      Category.assoc, hk, comp_zero, Preadditive.sub_comp] at h
  exact (sub_eq_zero.mp h.symm).symm

/-- The compatibility of the maps `n ↦ Sigma.ι _ n ≫ k`: for `n ≤ m` the `m`-th one precomposed
with the transition map is the `n`-th one.  Induction on `m` from `n`, the step being
`step_ι_comp`. -/
lemma telCocone_compat (F : ℕ ⥤ Cpx) {A : Cpx} (k : (∐ fun n => F.obj n) ⟶ A)
    (hk : telD F ≫ k = 0) {n m : ℕ} (h : n ≤ m) :
    F.map (homOfLE h) ≫ (Sigma.ι (fun n => F.obj n) m ≫ k) = Sigma.ι (fun n => F.obj n) n ≫ k := by
  let P : ∀ m : ℕ, n ≤ m → Prop := fun m h =>
    F.map (homOfLE h) ≫ (Sigma.ι (fun n => F.obj n) m ≫ k) = Sigma.ι (fun n => F.obj n) n ≫ k
  have base : P n (le_refl n) := by simp [P]
  have succ : ∀ m (hm : n ≤ m), P m hm → P (m+1) (Nat.le_succ_of_le hm) := by
    intro m hm ih
    show F.map (homOfLE (Nat.le_succ_of_le hm)) ≫ (Sigma.ι (fun n => F.obj n) (m+1) ≫ k)
      = Sigma.ι (fun n => F.obj n) n ≫ k
    rw [show (homOfLE (Nat.le_succ_of_le hm) : n ⟶ m+1) =
      homOfLE hm ≫ homOfLE (Nat.le_succ m) from Subsingleton.elim _ _]
    rw [F.map_comp]
    change F.map (homOfLE hm) ≫ (step F m ≫ (Sigma.ι (fun n => F.obj n) (m+1) ≫ k))
      = Sigma.ι (fun n => F.obj n) n ≫ k
    rw [step_ι_comp F k hk m]
    exact ih
  exact Nat.le_induction base succ m h

/-- The cocone over `F` whose `n`-th leg is `Sigma.ι _ n ≫ k`, for `k` killed by `telD F`. -/
noncomputable def telCocone (F : ℕ ⥤ Cpx) {A : Cpx} (k : (∐ fun n => F.obj n) ⟶ A)
    (hk : telD F ≫ k = 0) : Cocone F :=
  Cocone.mk A
  { app := fun n => Sigma.ι (fun n => F.obj n) n ≫ k
    naturality := fun {n m} f => by
      have h := telCocone_compat F k hk (leOfHom f)
      rw [Subsingleton.elim (homOfLE (leOfHom f)) f] at h
      simpa using h }

/-- The induced map `colim F ⟶ A` indeed factors `k` through `toColim F`. -/
lemma toColim_desc_telCocone (F : ℕ ⥤ Cpx) {A : Cpx} (k : (∐ fun n => F.obj n) ⟶ A)
    (hk : telD F ≫ k = 0) :
    toColim F ≫ colimit.desc F (telCocone F k hk) = k := by
  apply Sigma.hom_ext
  intro n
  rw [← Category.assoc, Sigma_ι_toColim, colimit.ι_desc]
  rfl

/-- The telescope short complex of a sequential diagram of cochain complexes,
`telShort F` (see `Submission.Work.TOOLKIT.SeqColim.Defs`), is exact.  Equivalently `toColim F` is
the cokernel of `telD F = 1 - shift`.

Route.  Prove `IsColimit (CokernelCofork.ofπ (f := telD F) (toColim F) (telD_toColim F))` and then
apply `ShortComplex.exact_of_g_is_cokernel (telShort F)` (note that `(telShort F).f = telD F`,
`(telShort F).g = toColim F`, `(telShort F).zero = telD_toColim F`, all definitional; see
`telShort_f`, `telShort_g`).
For the cokernel statement: given a cokernel cofork `t` (so `t.π : ∐_n F_n ⟶ W` with
`telD F ≫ t.π = 0`), the maps `n ↦ Sigma.ι _ n ≫ t.π : F.obj n ⟶ W` form a cocone over `F`: the
compatibility `F.map (homOfLE h) ≫ (Sigma.ι _ m ≫ t.π) = Sigma.ι _ n ≫ t.π` for `n ≤ m` follows by
`Nat.le_induction` from the case `h = Nat.le_succ n`, which is the component identity
`Sigma_ι_towerD` (`Sigma.ι X n ≫ towerD X i = Sigma.ι X n - i n ≫ Sigma.ι X (n+1)`, here
`X := fun n => F.obj n`, `i := step F`) together with `telD F ≫ t.π = 0` (use `Subsingleton.elim`
to identify the morphisms `homOfLE _` of `ℕ`).  Then `colimit.desc F thatCocone` is the required
factorisation, and uniqueness is `Limits.colimit.hom_ext` (or `epi_toColim`). -/
theorem exact_telShort (F : CategoryTheory.Functor ℕ Work.TOOLKIT.Cpx) :
    CategoryTheory.ShortComplex.Exact (Work.TOOLKIT.SeqColim.telShort F) := by
  have hcok : IsColimit (CokernelCofork.ofπ (f := telD F) (toColim F) (telD_toColim F)) :=
    CokernelCofork.IsColimit.ofπ' (f := telD F) (toColim F) (telD_toColim F)
      (fun {A} k hk => ⟨colimit.desc F (telCocone F k hk), toColim_desc_telCocone F k hk⟩)
      (hp := epi_toColim F)
  exact ShortComplex.exact_of_g_is_cokernel (telShort F) hcok

end Work.TOOLKIT.SeqColim
