import Mathlib
import Submission.Work.ORLinnell.Linnell
import Submission.Work.ORLinnell.FiniteIndex.TransversalDefs

/-!
# The finite index decomposition `D H = ∑_q (D H₀) · x_q` without a division ring hypothesis

Let `L : LinnellDatum K G U`, `H₀ ≤ H ≤ G` with `H₀` normal in `H` of finite index.  In
`Submission.Work.ORLinnell.FiniteIndex.TransversalDefs` we built the subring

`spanSub L hH₀ = ∑_{q ∈ H ⧸ H₀} (L.D H₀) · x_q ⊆ U`

of the `L.D H₀`-linear combinations of the coset representatives `x_q = gen (out q) ∈ U`, and
checked that it contains `L.D H₀`, the image of `K` and the images of all `h : H`.

Here we prove the remaining step, namely that `spanSub L hH₀` is *division closed* in `U`,
under the hypothesis that `L.D H₀` is a division ring, expressed as
`hdiv : ∀ x : ↥(L.D H₀), x ≠ 0 → IsUnit x` (so that no `DivisionRing` instance has to be
manufactured at the statement level, and the lemma applies verbatim when `H₀` is torsion free,
via `LinnellDatum.division_of_torsionFree`).

The argument is the classical one: `E := spanSub L hH₀` is a finite dimensional left vector
space over the division ring `D H₀` (it is the image of the finitely supported module
`(H ⧸ H₀) →₀ D H₀` under `xspan`).  If `x ∈ E` and `x * y = 1` in `U`, then right
multiplication `ρ_x : z ↦ z * x` is an injective `D H₀`-linear endomorphism of `E`, hence
surjective, and an `e ∈ E` with `e * x = 1` satisfies `e = y`.  Therefore `y ∈ E`.

By minimality of the division closure (`LinnellDatum.minimal`) it follows that
`L.D H ≤ spanSub L hH₀`, which is the statement `span_D_of_finiteIndex`.
-/

noncomputable section

namespace Work.ORLinnell.FiniteIndex

open Work.ORLinnell

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Nontrivial U]
  [Algebra K U]

/-- **Division closedness of the span `∑_q (D H₀) x_q`.**  If every nonzero element of `L.D H₀`
is a unit, then the subring `spanSub L hH₀` of `U` is closed under inverses in `U`.

The proof is the finite dimensional argument of L1(1): `spanSub L hH₀` is the image of the free
`D H₀`-module `(H ⧸ H₀.subgroupOf H) →₀ ↥(L.D H₀)` under `xspan`, so it is finite dimensional
over the division ring `D H₀`; right multiplication by an element of `spanSub L hH₀` which is
invertible in `U` is an injective `D H₀`-linear endomorphism of it, hence surjective. -/
theorem isDivisionClosed_spanSub (L : LinnellDatum K G U) {H₀ H : Subgroup G}
    (hH₀ : H₀ ≤ H) (hN : (H₀.subgroupOf H).Normal) (hfin : (H₀.subgroupOf H).FiniteIndex)
    (hdiv : ∀ x : ↥(L.D H₀), x ≠ 0 → IsUnit x) : IsDivisionClosed (spanSub L hH₀) := by
  classical
  haveI hN' : (H₀.subgroupOf H).Normal := hN
  -- `D H₀` is a division ring, by the hypothesis on nonzero elements.
  letI hDR : DivisionRing ↥(L.D H₀) :=
    DivisionRing.ofIsUnitOrEqZero fun x => by
      rcases eq_or_ne x 0 with h | h
      · exact Or.inr h
      · exact Or.inl (hdiv x h)
  -- the `D H₀`-module structure on the span, induced by the inclusion `D H₀ ≤ spanSub`.
  letI hMod : Module ↥(L.D H₀) ↥(spanSub L hH₀) := moduleOfLe (D_le_spanSub L hH₀)
  have hsmul : ∀ (d : ↥(L.D H₀)) (z : ↥(spanSub L hH₀)),
      ((d • z : ↥(spanSub L hH₀)) : U) = (d : U) * (z : U) := fun _ _ => rfl
  haveI hFintype : Fintype (H ⧸ H₀.subgroupOf H) := Subgroup.fintypeQuotientOfFiniteIndex
  -- `xspan` is a surjective `D H₀`-linear map, so the span is finite dimensional.
  let Φ : ((H ⧸ H₀.subgroupOf H) →₀ ↥(L.D H₀)) →ₗ[↥(L.D H₀)] ↥(spanSub L hH₀) :=
    { toFun := fun c => ⟨xspan L c, by show xspan L c ∈ spanSet L H₀ H; exact ⟨c, rfl⟩⟩
      map_add' := fun c c' => by
        apply Subtype.ext
        show xspan L (c + c') = xspan L c + xspan L c'
        rw [xspan_add]
      map_smul' := fun d c => by
        apply Subtype.ext
        show xspan L (d • c) = (d : U) * xspan L c
        rw [xspan_smul] }
  have hsurjΦ : Function.Surjective Φ := fun z => by
    obtain ⟨c, hc⟩ := z.2
    exact ⟨c, Subtype.ext hc.symm⟩
  haveI : FiniteDimensional ↥(L.D H₀) ↥(spanSub L hH₀) :=
    FiniteDimensional.of_surjective Φ hsurjΦ
  -- the main step: right multiplication by `x` is injective, hence surjective.
  intro x hx y hxy
  let xE : ↥(spanSub L hH₀) := ⟨x, hx⟩
  let ρ : ↥(spanSub L hH₀) →ₗ[↥(L.D H₀)] ↥(spanSub L hH₀) :=
    { toFun := fun z => z * xE
      map_add' := fun a b => by
        apply Subtype.ext
        show ((a : U) + (b : U)) * (xE : U) = (a : U) * (xE : U) + (b : U) * (xE : U)
        rw [add_mul]
      map_smul' := fun d z => by
        apply Subtype.ext
        show ((d : U) * (z : U)) * (xE : U) = (d : U) * ((z : U) * (xE : U))
        rw [mul_assoc] }
  have hinj : Function.Injective ρ := by
    intro a b hab
    have hab' : ((a : U) * x) = ((b : U) * x) := by
      have h := congrArg (fun t : ↥(spanSub L hH₀) => (t : U)) hab
      simpa [ρ, xE] using h
    apply Subtype.ext
    calc (a : U) = (a : U) * (x * y) := by rw [hxy, mul_one]
      _ = ((a : U) * x) * y := by rw [mul_assoc]
      _ = ((b : U) * x) * y := by rw [hab']
      _ = (b : U) * (x * y) := by rw [mul_assoc]
      _ = (b : U) := by rw [hxy, mul_one]
  have hsurjρ : Function.Surjective ρ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj
  -- a right inverse `e ∈ spanSub L hH₀` of `x`, which must coincide with `y`.
  obtain ⟨e, he⟩ := hsurjρ (1 : ↥(spanSub L hH₀))
  have he' : ((e : U) * x) = 1 := by
    have h := congrArg (fun t : ↥(spanSub L hH₀) => (t : U)) he
    simpa [ρ, xE] using h
  have hy : y = (e : U) := by
    calc y = 1 * y := (one_mul y).symm
      _ = ((e : U) * x) * y := by rw [← he']
      _ = (e : U) * (x * y) := by rw [mul_assoc]
      _ = (e : U) := by rw [hxy, mul_one]
  rw [hy]
  exact e.2

/-- **L1(1), finite index case.**  If `H₀ ≤ H` is normal in `H` of finite index and `D H₀` is a
division ring (in the form "every nonzero element of `L.D H₀` is a unit"), then every element of
`L.D H` is a finite sum `∑_q d_q * gen (out q)` with `d_q ∈ L.D H₀`, `q` running over the
cosets `H ⧸ H₀`. -/
theorem span_D_of_finiteIndex {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Nontrivial U] [Algebra K U] (L : Work.ORLinnell.LinnellDatum K G U) {H₀ H : Subgroup G}
    (hH₀ : H₀ ≤ H) (hN : (H₀.subgroupOf H).Normal) (hfin : (H₀.subgroupOf H).FiniteIndex)
    (hdiv : ∀ x : ↥(L.D H₀), x ≠ 0 → IsUnit x) (y : U) (hy : y ∈ L.D H) :
    ∃ c : (H ⧸ H₀.subgroupOf H) →₀ ↥(L.D H₀),
      y = c.sum (fun q d => (d : U) * (L.gen ((Quotient.out q : H) : G) : U)) := by
  haveI hN' : (H₀.subgroupOf H).Normal := hN
  -- `spanSub L hH₀` contains `L.D H₀`, the image of `K` and the image of `H`, and it is division
  -- closed, so it contains the division closure `L.D H`.
  have hle : L.D H ≤ spanSub L hH₀ :=
    L.minimal H (spanSub L hH₀)
      (fun h => gen_mem_spanSet L hH₀ h)
      (fun k => algebraMap_mem_spanSet L hH₀ k)
      (isDivisionClosed_spanSub L hH₀ hN hfin hdiv)
  obtain ⟨c, hc⟩ := hle hy
  exact ⟨c, by simpa only [xspan, cosetX, cosetXU] using hc⟩

end Work.ORLinnell.FiniteIndex
