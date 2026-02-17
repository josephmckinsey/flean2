# flean2

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.

TODO: Do we need IsRoundUpOn and IsRoundDownOn?
TODO: Do we need that gluing preserves IsRoundUp and IsRoundDown?

Why isn't grind automatically accessing the member elements of approx?

TODO List:
- [X] Ring operations on rounders (addition, multiplication)
- [ ] Figure out why grind isn't unpacking approx elements automatically.
- [X] FloorRings have round_down = floor and round_up = ceil.
- [X] Minimum and maximum element lemmas
- [X] Gluing operations: binary and Σ based.
- [ ] Adding new bottom and top elements (not a priority, may be unnecessary)
- [X] Bound with an interval [a, b]
- [ ] Fix todos
- [ ] Try bound tactic at each line
